"""Resume the remaining endpoint certificates with immutable inputs and receipts."""
from pathlib import Path
import datetime,hashlib,json,os,subprocess,sys,time
H=Path(__file__).resolve().parents[1]
read=lambda p:json.loads(p.read_text(encoding='utf-8-sig'))
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
planpath=H/'data/pending-plan.json';plan=read(planpath)
for p,d in plan['pins'].items():assert sha(H/p)==d,p
lock=H/'data/pending.lock';run=str(time.time_ns())
with lock.open('x') as f:json.dump(dict(pid=os.getpid(),run=run),f)
record=H/'logs'/('pending-'+run+'.json');progress=H/'data/pending-progress.json'
state=dict(status='STARTING',pid=os.getpid(),started_at=datetime.datetime.now(datetime.timezone.utc).isoformat(),
    plan_sha256=sha(planpath),driver_sha256=sha(Path(__file__)),modules=plan['modules'],active=None)
def save():
    data=json.dumps(state,indent=2)+'\n';record.write_text(data);progress.write_text(data)
save()
try:
    assert not (H/'data/check.lock').exists(),'A proof checker is already active; inspect its process before resuming.'
    log=H/'logs'/('pending-'+run+'.log')
    with log.open('w',encoding='utf-8') as out:
        p=subprocess.Popen([sys.executable,'-B','-X','utf8',str(H/'scripts/check_isolated.py'),*plan['modules']],
            cwd=H.parents[1],stdout=out,stderr=subprocess.STDOUT)
        state.update(status='RUNNING',active=dict(checker_pid=p.pid,log=log.relative_to(H).as_posix()));save()
        code=p.wait()
    state['active']=None
    for p,d in plan['pins'].items():assert sha(H/p)==d,p
    assert code==0,('Checker failed; inspect preserved log',str(log),code)
    for m in plan['modules']:
        r=read(H/'data'/(m+'-audit.json'))
        assert r['status']=='PASS_REFERENCE_RECOVERY_MODULE' and r['exit_code']==0 and not r['timeout']
    state['status']='PASS_ALL_ENDPOINT_CERTIFICATES_AND_ACTUAL_ASSEMBLY'
except BaseException as exc:
    state.update(status='STOPPED',exception=repr(exc));raise
finally:
    state['stopped_at']=datetime.datetime.now(datetime.timezone.utc).isoformat();save()
    if state['active'] is None:lock.unlink()
