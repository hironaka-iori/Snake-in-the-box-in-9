"""Check compatible credit sources sequentially, preserving attempts and pins."""
from pathlib import Path
import argparse,datetime,hashlib,json,os,re,subprocess,time
HERE=Path(__file__).resolve().parents[1];ROOT=HERE.parents[1];OLD=HERE.parent/'94-history-share-dispatch'
BIN=Path('D:/Codex/2026-10-01/it-should-have-a-property-of/work/lean-research/lean-4.19.0-windows/bin')
read=lambda p:json.loads(p.read_text(encoding='utf-8-sig'));sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
parser=argparse.ArgumentParser();parser.add_argument('modules',nargs='+');args=parser.parse_args()
run=str(time.time_ns());rp=HERE/'logs'/('check-run-'+run+'.json');lock=HERE/'data/check.lock'
state=dict(status='RUNNING',pid=os.getpid(),started_at=datetime.datetime.now(datetime.timezone.utc).isoformat(),modules=args.modules,records=[],active=None)
def save():rp.write_text(json.dumps(state,indent=2)+'\n')
with lock.open('x') as out:json.dump(dict(pid=os.getpid(),run_record=str(rp)),out)
paths=[str(HERE/'build'),str(OLD/'build')]
# Preserve the graph's module-prefix ordering: appending its support directories
# behind an older LocalWindowSat directory selects the wrong namespace root.
for path in read(HERE.parent/'92-full-witness-batch/data/DefinedProofGraph-audit.json')['paths'] + read(OLD/'data/HistoryShareCaps-audit.json')['paths']:
    if path not in paths:paths.append(path)
env=os.environ.copy();env['PATH']=str(BIN)+';'+env['PATH'];env['LEAN_PATH']=';'.join(paths)
attempt=HERE/'logs'/('attempt-'+run);attempt.mkdir()
(attempt/'checker.py.txt').write_bytes(Path(__file__).read_bytes())
checker=sha(Path(__file__))
def pins(module):
    dependencies={}
    for name in ['HistoryShareCover','HistoryShareCaps','HistoryShareAssembly','HistoryShareValidity','HistoryShareCounts']:
        receipt=OLD/'data'/(name+'-audit.json');r=read(receipt)
        assert r['exit_code']==0 and r['status']=='PASS_HISTORY_SHARE_MODULE'
        assert sha(OLD/'lean'/(name+'.lean'))==r['source_sha256'] and sha(OLD/'build'/(name+'.olean'))==r['olean_sha256'] and sha(OLD/r['log'])==r['log_sha256']
        dependencies[receipt.relative_to(ROOT).as_posix()]=sha(receipt)
    source=HERE/'lean'/(module+'.lean')
    imports=re.findall(r'^import ([\w.]+)$',source.read_text(),re.M)
    for name in imports:
        dep=HERE/'lean'/(name+'.lean')
        if dep.exists():
            receipt=HERE/'data'/(name+'-audit.json');r=read(receipt)
            assert r['exit_code']==0 and r['status']=='PASS_COMPATIBLE_CREDIT_MODULE'
            assert sha(dep)==r['source_sha256'] and sha(HERE/'build'/(name+'.olean'))==r['olean_sha256'] and sha(HERE/r['log'])==r['log_sha256']
            dependencies[receipt.relative_to(ROOT).as_posix()]=sha(receipt)
        else:
            candidates=[Path(p)/(name.replace('.','/')+'.olean') for p in paths]
            found=next((p for p in candidates if p.exists()),None)
            if found is not None:dependencies[found.relative_to(ROOT).as_posix()]=sha(found)
            else:assert name.startswith('Mathlib.'),('Unresolved direct import',name)
    return dependencies
save()
try:
    for name in args.modules:
        src=HERE/'lean'/(name+'.lean');before=sha(src);deps=pins(name)
        rp_a=HERE/'data'/(name+'-audit.json');obj=HERE/'build'/(name+'.olean')
        if rp_a.exists():
            r=read(rp_a)
            assert r['source_sha256']==before and r['dependencies']==deps and sha(obj)==r['olean_sha256'] and sha(HERE/r['log'])==r['log_sha256']
            state['records'].append(dict(module=name,status='REUSED',receipt_sha256=sha(rp_a)));save();print(name,'REUSED',flush=True);continue
        (attempt/(name+'.lean.txt')).write_bytes(src.read_bytes())
        command="@(Get-CimInstance Win32_Process -Filter \"Name='lean.exe'\" | Select-Object ProcessId,PrivatePageCount) | ConvertTo-Json -Compress"
        while True:
            raw=subprocess.check_output(['powershell','-NoProfile','-Command',command],text=True).strip();others=json.loads(raw) if raw else []
            if isinstance(others,dict):others=[others]
            if len(others)<=2 and sum(int(p['PrivatePageCount']) for p in others)<8*1024**3:break
            state.update(status='WAITING_FOR_COMPILER_SLOT',active=None,waiting_for=name,other_processes=others);save();time.sleep(10)
        assert sha(src)==before and pins(name)==deps and sha(Path(__file__))==checker
        log=HERE/'logs'/(name+'-'+run+'.log');fresh=HERE/'build'/(name+'.'+run+'.olean');start=time.monotonic();timedout=False
        with log.open('w',encoding='utf-8') as out:
            proc=subprocess.Popen([str(BIN/'lake.exe'),'env','lean','-s','65536','-R',str(HERE/'lean'),'-o',str(fresh),str(src)],cwd=BIN.parent.parent/'mathlib',env=env,stdout=out,stderr=subprocess.STDOUT)
            state.update(status='RUNNING',active=dict(module=name,launcher_pid=proc.pid,source_sha256=before,log=str(log)));save()
            try:code=proc.wait(timeout=300)
            except subprocess.TimeoutExpired:
                timedout=True
                subprocess.run(['taskkill','/PID',str(proc.pid),'/T','/F'],stdout=subprocess.DEVNULL,stderr=subprocess.DEVNULL,check=False)
                code=proc.wait(timeout=30)
        state['active']=None;save()
        r=dict(module=name,exit_code=code,timeout=timedout,seconds=time.monotonic()-start,source_sha256=before,
               log=log.relative_to(HERE).as_posix(),log_sha256=sha(log),dependencies=deps,paths=paths,checker_sha256=checker,
               source_snapshot=(attempt/(name+'.lean.txt')).relative_to(HERE).as_posix())
        (HERE/'logs'/(name+'-'+run+'-record.json')).write_text(json.dumps(r,indent=2)+'\n')
        assert not timedout and code==0,log.read_text()[-14000:]
        assert sha(src)==before and pins(name)==deps and sha(Path(__file__))==checker
        output=log.read_text();assert 'error:' not in output and 'sorryAx' not in output
        assert not re.search(r'\b(sorry|admit|native_decide)\b',src.read_text())
        rows=re.findall(r"'([^']+)' depends on axioms:\s*\[([^]]*)\]",output,re.S)
        rows += [(n,'') for n in re.findall(r"'([^']+)' does not depend on any axioms",output)]
        assert len(rows)==src.read_text().count('#print axioms') and rows
        audits=[]
        for theorem,ax in rows:
            axioms=re.findall(r'[A-Za-z][\w.]*',ax);assert set(axioms)<={'propext','Classical.choice','Quot.sound'}
            audits.append(dict(theorem=theorem,axioms=axioms))
        os.replace(fresh,obj)
        r.update(status='PASS_COMPATIBLE_CREDIT_MODULE',olean_sha256=sha(obj),theorem_audits=audits,
                 scope='Stated compatible local-credit or transport/evaluator theorem only. Global numerical bound and uninstantiated premises remain separate.')
        rp_a.write_text(json.dumps(r,indent=2)+'\n')
        state['records'].append(dict(module=name,status=r['status'],receipt_sha256=sha(rp_a),theorem_audits=len(audits)))
        save();print(name,'PASS',round(r['seconds'],3),'seconds;',len(audits),'audits',flush=True)
    state['status']='PASS_REQUESTED_MODULES'
except BaseException as exc:
    state.update(status='STOPPED',exception=repr(exc));raise
finally:
    state['stopped_at']=datetime.datetime.now(datetime.timezone.utc).isoformat();save()
    if state['active'] is None:lock.unlink()
