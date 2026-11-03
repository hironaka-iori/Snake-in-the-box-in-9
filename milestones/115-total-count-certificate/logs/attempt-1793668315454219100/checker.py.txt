"""Check selected Lean modules with pinned dependencies and unique attempt receipts."""
from pathlib import Path
import argparse,datetime,hashlib,json,os,re,subprocess,time
HERE=Path(__file__).resolve().parents[1];ROOT=HERE.parents[1]
OLD=ROOT/'milestones/112-critical-sum-refinement';TRANSFER=ROOT/'milestones/114-total-count-pressure'
BIN=Path('D:/Codex/2026-10-01/it-should-have-a-property-of/work/lean-research/lean-4.19.0-windows/bin')
read=lambda p:json.loads(p.read_text(encoding='utf-8-sig'))
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
p=argparse.ArgumentParser();p.add_argument('modules',nargs='+');p.add_argument('--timeout',type=int,default=180);args=p.parse_args()
for d in ['logs','data','build']:(HERE/d).mkdir(exist_ok=True)
run=str(time.time_ns());record=HERE/'logs'/('check-run-'+run+'.json');lock=HERE/'data/check.lock'
state=dict(status='PREPARED',pid=os.getpid(),started_at=datetime.datetime.now(datetime.timezone.utc).isoformat(),modules=args.modules,records=[],active=None)
def save():record.write_text(json.dumps(state,indent=2)+'\n',encoding='utf-8')
environment_path=OLD/'data/environment-isolated.json';environment=read(environment_path)
paths=[str(HERE/'build'),str(TRANSFER/'build-total-geometry')]+environment['paths']
base={str(environment_path):sha(environment_path),str(BIN/'lean.exe'):sha(BIN/'lean.exe'),
      str(BIN/'lake.exe'):sha(BIN/'lake.exe'),str(BIN.parent.parent/'mathlib/lake-manifest.json'):sha(BIN.parent.parent/'mathlib/lake-manifest.json')}
for rel,digest in environment['receipts'].items():
    path=ROOT/rel;assert sha(path)==digest;base[str(path)]=digest
for home,name,build in [(OLD,'SumCountSemantics112','build-sum-semantics'),(TRANSFER,'TotalGeometry114','build-total-geometry')]:
    receipt=home/'data'/(name+'-audit.json');r=read(receipt);assert r['exit_code']==0 and not r['timeout'] and r['status'].startswith('PASS_')
    for path,digest in [(receipt,sha(receipt)),(home/'lean'/(name+'.lean'),r['source_sha256']),
                       (home/build/(name+'.olean'),r['olean_sha256']),(home/r['log'],r['log_sha256'])]:
        assert sha(path)==digest;base[str(path)]=digest
    for rel,digest in r['dependencies'].items():
        path=Path(rel);path=path if path.is_absolute() else ROOT/path
        assert sha(path)==digest;base[str(path)]=digest
env=os.environ.copy();env['PATH']=str(BIN)+';'+env['PATH'];env['LEAN_PATH']=';'.join(paths)
attempt=HERE/'logs'/('attempt-'+run);attempt.mkdir();(attempt/'checker.py.txt').write_bytes(Path(__file__).read_bytes())
checker=sha(Path(__file__))
def pins(module):
    dependencies=dict(base)
    source=HERE/'lean'/(module.replace('.','/')+'.lean')
    for name in re.findall(r'^import ([\w.]+)$',source.read_text(encoding='utf-8'),re.M):
        dep=HERE/'lean'/(name.replace('.','/')+'.lean')
        obj=next((Path(p)/(name.replace('.','/')+'.olean') for p in paths if (Path(p)/(name.replace('.','/')+'.olean')).exists()),None)
        if dep.exists():
            receipt=HERE/'data'/(name+'-audit.json');r=read(receipt)
            assert r['status']=='PASS_TOTAL_COUNT_MODULE' and r['exit_code']==0 and not r['timeout']
            assert sha(dep)==r['source_sha256'] and obj is not None and sha(obj)==r['olean_sha256'] and sha(HERE/r['log'])==r['log_sha256']
            dependencies[str(receipt)]=sha(receipt);dependencies[str(dep)]=sha(dep)
        assert obj is not None,('Unresolved import',name)
        dependencies[str(obj)]=sha(obj)
    for path,digest in dependencies.items():assert sha(Path(path))==digest,path
    return dependencies
with lock.open('x') as f:json.dump(dict(pid=os.getpid(),run_record=str(record)),f)
save()
try:
    for name in args.modules:
        source=HERE/'lean'/(name.replace('.','/')+'.lean');before=sha(source);deps=pins(name)
        receipt=HERE/'data'/(name+'-audit.json');obj=HERE/'build'/(name.replace('.','/')+'.olean');obj.parent.mkdir(parents=True,exist_ok=True)
        if receipt.exists():
            r=read(receipt);assert r['status']=='PASS_TOTAL_COUNT_MODULE' and r['source_sha256']==before and r['dependencies']==deps and sha(obj)==r['olean_sha256'] and sha(HERE/r['log'])==r['log_sha256']
            state['records'].append(dict(module=name,status='REUSED',receipt_sha256=sha(receipt)));save();print(name,'REUSED',flush=True);continue
        assert not re.search(r'\b(sorry|admit|native_decide)\b',source.read_text(encoding='utf-8'))
        snapshot=attempt/(name+'.lean.txt');snapshot.write_bytes(source.read_bytes())
        query="@(Get-CimInstance Win32_Process -Filter \"Name='lean.exe'\" | Select-Object ProcessId,PrivatePageCount) | ConvertTo-Json -Compress"
        while True:
            raw=subprocess.check_output(['powershell','-NoProfile','-Command',query],text=True).strip();others=json.loads(raw) if raw else []
            if isinstance(others,dict):others=[others]
            if len(others)<=1 and sum(int(x['PrivatePageCount']) for x in others)<8*1024**3:break
            state.update(status='WAITING_FOR_COMPILER_SLOT',waiting_for=name,other_processes=others);save();time.sleep(10)
        assert sha(source)==before and pins(name)==deps and sha(Path(__file__))==checker
        log=HERE/'logs'/(name+'-'+run+'.log');fresh=obj.with_name(obj.stem+'.'+run+'.olean')
        command=[str(BIN/'lake.exe'),'env','lean','-s','65536','-R',str(HERE/'lean'),'-o',str(fresh),str(source)]
        start=time.monotonic();timeout=False
        with log.open('w',encoding='utf-8') as output:
            proc=subprocess.Popen(command,cwd=BIN.parent.parent/'mathlib',env=env,stdout=output,stderr=subprocess.STDOUT)
            state.update(status='RUNNING',active=dict(module=name,pid=proc.pid,log=str(log)),command=command);save()
            try:code=proc.wait(timeout=args.timeout)
            except subprocess.TimeoutExpired:
                timeout=True;subprocess.run(['taskkill','/PID',str(proc.pid),'/T','/F'],stdout=subprocess.DEVNULL,stderr=subprocess.DEVNULL,check=False);code=proc.wait(timeout=30)
        state['active']=None;save()
        r=dict(module=name,exit_code=code,timeout=timeout,seconds=time.monotonic()-start,source_sha256=before,
            log=log.relative_to(HERE).as_posix(),log_sha256=sha(log),dependencies=deps,paths=paths,
            checker_sha256=checker,source_snapshot=snapshot.relative_to(HERE).as_posix(),command=command)
        (HERE/'logs'/(name+'-'+run+'-record.json')).write_text(json.dumps(r,indent=2)+'\n',encoding='utf-8')
        assert code==0 and not timeout,log.read_text(encoding='utf-8')[-6000:]
        assert sha(source)==before and pins(name)==deps and sha(Path(__file__))==checker
        text=log.read_text(encoding='utf-8');assert 'error:' not in text and 'sorryAx' not in text
        rows=re.findall(r"'([^']+)' depends on axioms:\s*\[([^]]*)\]",text,re.S)
        rows += [(n,'') for n in re.findall(r"'([^']+)' does not depend on any axioms",text)]
        assert len(rows)==source.read_text(encoding='utf-8').count('#print axioms')
        audits=[]
        for theorem,ax in rows:
            axioms=re.findall(r'[A-Za-z][\w.]*',ax);assert set(axioms)<={'propext','Classical.choice','Quot.sound'}
            audits.append(dict(theorem=theorem,axioms=axioms))
        os.replace(fresh,obj);r.update(status='PASS_TOTAL_COUNT_MODULE',olean_sha256=sha(obj),theorem_audits=audits,
            scope='This exact concrete total-count proof module only; all generated or unchecked modules remain pending.')
        receipt.write_text(json.dumps(r,indent=2)+'\n',encoding='utf-8')
        state['records'].append(dict(module=name,status=r['status'],receipt_sha256=sha(receipt),theorem_audits=len(audits)))
        save();print(name,'PASS',round(r['seconds'],3),len(audits),'axiom reports',flush=True)
    state['status']='PASS_REQUESTED_MODULES'
except BaseException as exc:
    state.update(status='STOPPED',exception=repr(exc));raise
finally:
    state['stopped_at']=datetime.datetime.now(datetime.timezone.utc).isoformat();save()
    if state['active'] is None:lock.unlink()
