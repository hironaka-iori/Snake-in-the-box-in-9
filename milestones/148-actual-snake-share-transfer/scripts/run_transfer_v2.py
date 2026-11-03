"""Resume minimal generic and concrete checks, one bounded Lean process at a time."""
from pathlib import Path
import argparse,datetime,hashlib,json,os,subprocess,sys,time
H=Path(__file__).resolve().parents[1];R=H.parents[1]
read=lambda p:json.loads(p.read_text(encoding='utf-8-sig'))
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
ap=argparse.ArgumentParser();ap.add_argument('--limit',type=int);ap.add_argument('--timeout',type=int,default=180);a=ap.parse_args()
planpath=H/'data/transfer-plan-v2.json';plan=read(planpath)
assert plan['status']=='PREPARED_TRANSFER_WITH_PINNED_DATA_OBJECT'
sources={x['path']:x['sha256'] for x in plan['artifacts']}
assert a.limit is None or a.limit>0
lock=H/'data/transfer-v2-batch.lock';stamp=str(time.time_ns())
record=H/'logs'/('transfer-v2-batch-'+stamp+'.json');progress=H/'data/transfer-v2-progress.json'
with lock.open('x') as f:json.dump(dict(pid=os.getpid(),record=record.relative_to(H).as_posix()),f)
state=dict(status='RUNNING',pid=os.getpid(),started_at=datetime.datetime.now(datetime.timezone.utc).isoformat(),
    total_modules=len(plan['module_order']),checked_modules=[],active=None,plan_sha256=sha(planpath),
    driver_sha256=sha(__file__),checker_sha256=sha(H/'scripts/check_module_v2.py'),requested_new_module_limit=a.limit,
    scope='Fresh transfer chain and actual-snake consequences with explicit local-refutation or core-Unsat premises. Complete contradiction remains separate.')
def save():
    state['updated_at']=datetime.datetime.now(datetime.timezone.utc).isoformat()
    s=json.dumps(state,indent=2)+'\n';record.write_text(s,encoding='utf-8',newline='\n');progress.write_text(s,encoding='utf-8',newline='\n')
def valid(m):
    rp=H/'data'/(m+'-audit.json')
    if not rp.exists():return None
    j=read(rp);assert j['status']=='PASS' and j['exit_code']==0 and j['stop_reason'] is None
    p=H/'lean'/(m.replace('.','/')+'.lean')
    assert sha(p)==j['source_sha256']==sources[p.relative_to(H).as_posix()]
    assert sha(j['object'])==j['olean_sha256'] and sha(j['log'])==j['log_sha256']
    assert sha(Path(j['log']).parent/'checker.py.txt')==j['checker_sha256']
    assert sha(Path(j['log']).parent/'source.lean.txt')==j['source_sha256']
    for p,d in j['dependencies'].items():assert sha(p)==d,p
    assert all(set(x['axioms'])<={'propext','Classical.choice','Quot.sound'} for x in j['axioms'])
    return dict(module=m,receipt_sha256=sha(rp),seconds=j['seconds'],compiler_wall_seconds=j['compiler_wall_seconds'],axiom_reports=len(j['axioms']))
save();count=0
try:
    for m in plan['module_order']:
        assert sha(__file__)==state['driver_sha256'] and sha(H/'scripts/check_module_v2.py')==state['checker_sha256']
        item=valid(m)
        if item is None:
            if a.limit is not None and count>=a.limit:
                state['status']='PASS_BOUNDED_TRANSFER_PREFIX';break
            p=H/'lean'/(m.replace('.','/')+'.lean');assert sha(p)==sources[p.relative_to(H).as_posix()]
            log=H/'logs'/('transfer-v2-launch-'+stamp+'-'+m+'.log')
            with log.open('w',encoding='utf-8') as out:
                child=subprocess.Popen([sys.executable,'-B','-X','utf8',str(H/'scripts/check_module_v2.py'),m,'--timeout',str(a.timeout)],stdout=out,stderr=subprocess.STDOUT,cwd=R)
                state['active']=dict(module=m,pid=child.pid,log=log.relative_to(H).as_posix());save();code=child.wait()
            state['active']=None;save();assert code==0,(m,code)
            item=valid(m);assert item is not None;count+=1
        state['checked_modules'].append(item);save();print('CHECKED',len(state['checked_modules']),'/',state['total_modules'],m,flush=True)
    else:state['status']='PASS_COMPLETE_CONDITIONAL_TRANSFER_CHAIN'
except BaseException as e:
    state['status']='STOPPED_ON_FAILED_OR_INCOMPLETE_MODULE';state['exception']=repr(e);raise
finally:
    state['finished_at']=datetime.datetime.now(datetime.timezone.utc).isoformat();save();lock.unlink()
    print(state['status'],flush=True)
