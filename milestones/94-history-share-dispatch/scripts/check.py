"""Sequential checks of complete history-share covers, with pinned dependencies."""
from pathlib import Path
import argparse,datetime,hashlib,json,os,re,subprocess,time
HERE=Path(__file__).resolve().parents[1];ROOT=HERE.parents[1];OLD=HERE.parent/'84-history-exclusion-retention'
BIN=Path('D:/Codex/2026-10-01/it-should-have-a-property-of/work/lean-research/lean-4.19.0-windows/bin')
read=lambda p:json.loads(p.read_text(encoding='utf-8-sig'));sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
parser=argparse.ArgumentParser();parser.add_argument('modules',nargs='+');args=parser.parse_args()
run=str(time.time_ns());rp=HERE/'logs'/('check-run-'+run+'.json');lock=HERE/'data/check.lock'
state=dict(status='RUNNING',pid=os.getpid(),started_at=datetime.datetime.now(datetime.timezone.utc).isoformat(),modules=args.modules,records=[],active=None)
def save():rp.write_text(json.dumps(state,indent=2)+'\n')
with lock.open('x') as out:json.dump(dict(pid=os.getpid(),run_record=str(rp)),out)
paths=[str(HERE/'build')]+read(OLD/'data/HistoryUnique-audit.json')['paths']
if str(OLD/'build') not in paths:paths.insert(1,str(OLD/'build'))
env=os.environ.copy();env['PATH']=str(BIN)+';'+env['PATH'];env['LEAN_PATH']=';'.join(paths)
def pins(module):
    dependencies={}
    for name in ['HistoryUnique','HistoryWindow','HistoryRealizations']:
        receipt=OLD/'data'/(name+'-audit.json');r=read(receipt)
        assert r['exit_code']==0 and r['status'].startswith('PASS_')
        for folder,ext,key in [('lean','.lean','source_sha256'),('build','.olean','olean_sha256'),('logs','.log','log_sha256')]:assert sha(OLD/folder/(name+ext))==r[key]
        dependencies[receipt.relative_to(ROOT).as_posix()]=sha(receipt)
    source=HERE/'lean'/(module+'.lean')
    for name in re.findall(r'^import (\w+)$',source.read_text(),re.M):
        dep=HERE/'lean'/(name+'.lean')
        if not dep.exists():continue
        receipt=HERE/'data'/(name+'-audit.json');r=read(receipt)
        assert r['exit_code']==0 and r['status']=='PASS_HISTORY_SHARE_MODULE'
        assert sha(dep)==r['source_sha256'] and sha(HERE/'build'/(name+'.olean'))==r['olean_sha256']
        assert sha(HERE/r['log'])==r['log_sha256']
        dependencies[receipt.relative_to(ROOT).as_posix()]=sha(receipt)
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
        # Only the two previously inspected batches may be running beside this one.
        command="@(Get-CimInstance Win32_Process -Filter \"Name='lean.exe'\" | Select-Object ProcessId,PrivatePageCount) | ConvertTo-Json -Compress"
        while True:
            raw=subprocess.check_output(['powershell','-NoProfile','-Command',command],text=True).strip();others=json.loads(raw) if raw else []
            if isinstance(others,dict):others=[others]
            if len(others)<=2 and sum(int(p['PrivatePageCount']) for p in others)<8*1024**3:break
            state.update(status='WAITING_FOR_COMPILER_SLOT',active=None,waiting_for=name,other_processes=others);save();time.sleep(10)
        assert sha(src)==before and pins(name)==deps
        log=HERE/'logs'/(name+'-'+run+'.log');fresh=HERE/'build'/(name+'.'+run+'.olean');start=time.monotonic();timedout=False
        with log.open('w',encoding='utf-8') as out:
            proc=subprocess.Popen([str(BIN/'lake.exe'),'env','lean','-s','65536','-R',str(HERE/'lean'),'-o',str(fresh),str(src)],cwd=BIN.parent.parent/'mathlib',env=env,stdout=out,stderr=subprocess.STDOUT)
            state.update(status='RUNNING',active=dict(module=name,launcher_pid=proc.pid,source_sha256=before,log=str(log)));save()
            try:code=proc.wait(timeout=300)
            except subprocess.TimeoutExpired:
                timedout=True
                subprocess.run(['taskkill','/PID',str(proc.pid),'/T','/F'],stdout=subprocess.DEVNULL,stderr=subprocess.DEVNULL,check=False)
                code=proc.wait(timeout=30)
        r=dict(module=name,exit_code=code,timeout=timedout,seconds=time.monotonic()-start,source_sha256=before,
               log=log.relative_to(HERE).as_posix(),log_sha256=sha(log),dependencies=deps,paths=paths,checker_sha256=sha(Path(__file__)))
        (HERE/'logs'/(name+'-'+run+'-record.json')).write_text(json.dumps(r,indent=2)+'\n')
        assert not timedout and code==0,log.read_text()[-14000:]
        assert sha(src)==before and pins(name)==deps
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
        r.update(status='PASS_HISTORY_SHARE_MODULE',olean_sha256=sha(obj),theorem_audits=audits,
                 scope='Complete signature realization covers and stated dispatch only. Concrete credit premises and full global charge remain separate.')
        rp_a.write_text(json.dumps(r,indent=2)+'\n')
        state['records'].append(dict(module=name,status=r['status'],receipt_sha256=sha(rp_a),theorem_audits=len(audits)))
        state['active']=None;save();print(name,'PASS',round(r['seconds'],3),'seconds;',len(audits),'audits',flush=True)
    state['status']='PASS_REQUESTED_MODULES'
except BaseException as exc:
    state.update(status='STOPPED',exception=repr(exc));raise
finally:
    state['stopped_at']=datetime.datetime.now(datetime.timezone.utc).isoformat();save()
    # On an interrupted active child, keep the lock until actual process inspection.
    if state['active'] is None:lock.unlink()
