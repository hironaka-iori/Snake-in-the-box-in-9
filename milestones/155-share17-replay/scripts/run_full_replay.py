"""Resume minimal generic and concrete checks, one bounded Lean process at a time."""
from pathlib import Path
import argparse,datetime,hashlib,json,os,subprocess,sys,time
H=Path(__file__).resolve().parents[1];R=H.parents[1]
read=lambda p:json.loads(p.read_text(encoding='utf-8-sig'))
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
ap=argparse.ArgumentParser();ap.add_argument('--limit',type=int);ap.add_argument('--timeout',type=int,default=180);a=ap.parse_args()
planpath=H/'data/full-source-plan.json';plan=read(planpath)
assert plan['status']=='SOURCE_PREPARED_UNCHECKED'
prep=read(H/'data/full-execution-preparation.json')
assert prep['status']=='PREPARED_FULL_SHARED_CORE_REPLAY_UNCHECKED'
assert sha(planpath)==prep['full_plan_sha256']
assert len(plan['module_order'])==137
assert not (H/'data/replay-batch-v2.lock').exists(), 'Wait for the pilot driver to finish'
for p,d in prep['input_pins'].items():assert sha(R/p)==d,p
assert sha(Path(__file__))==prep['execution_scripts_sha256']['scripts/run_full_replay.py']
assert sha(H/'scripts/check_full_replay.py')==prep['execution_scripts_sha256']['scripts/check_full_replay.py']
for p,d in prep['original_source_pins'].items():assert sha(R/p)==d,p
sources={x['path']:x['sha256'] for x in plan['artifacts']}
assert a.limit is None or a.limit>0
assert not (H/'data/replay-batch.lock').exists(), 'Inspect original driver before launching v2'
assert sha(H/'scripts/native_resources.py')==prep['resource_helper_sha256']
(H/'logs').mkdir(parents=True,exist_ok=True)
lock=H/'data/full-replay-batch.lock';stamp=str(time.time_ns())
record=H/'logs'/('full-replay-batch-'+stamp+'.json');progress=H/'data/full-replay-progress.json'
with lock.open('x') as f:json.dump(dict(pid=os.getpid(),record=record.relative_to(H).as_posix()),f)
state=dict(status='RUNNING',pid=os.getpid(),started_at=datetime.datetime.now(datetime.timezone.utc).isoformat(),
    total_modules=len(plan['module_order']),checked_modules=[],active=None,plan_sha256=sha(planpath),
    driver_sha256=sha(__file__),checker_sha256=sha(H/'scripts/check_full_replay.py'),requested_new_module_limit=a.limit,
    scope='Complete shared153 core contradiction, reusing the34 accepted pilot modules. Actual-snake composition remains separate.')
def save():
    state['updated_at']=datetime.datetime.now(datetime.timezone.utc).isoformat()
    s=json.dumps(state,indent=2)+'\n';record.write_text(s,encoding='utf-8',newline='\n');progress.write_text(s,encoding='utf-8',newline='\n')
def valid(m):
    rp=H/'data'/(m+'-audit.json')
    if not rp.exists():
        assert m not in prep['reused_pilot_receipts'], 'An accepted pilot receipt is missing; inspect it instead of recompiling'
        return None
    j=read(rp);assert j['status']=='PASS' and j['exit_code']==0 and j['stop_reason'] is None
    p=H/'lean'/(m.replace('.','/')+'.lean')
    assert sha(p)==j['source_sha256']==sources[p.relative_to(H).as_posix()]
    assert sha(j['object'])==j['olean_sha256'] and sha(j['log'])==j['log_sha256']
    assert sha(Path(j['log']).parent/'checker.py.txt')==j['checker_sha256']
    assert sha(Path(j['log']).parent/'source.lean.txt')==j['source_sha256']
    for p,d in j['dependencies'].items():assert sha(p)==d,p
    if m in prep['reused_pilot_receipts']:
        previous=prep['reused_pilot_receipts'][m]
        assert sha(rp)==previous['receipt_sha256'] and j['checker_sha256']==previous['checker_sha256']
    else:
        assert j['checker_sha256']==sha(H/'scripts/check_full_replay.py')
    assert len(j['axioms'])==Path(j['source']).read_text(encoding='utf-8').count('#print axioms')
    assert all(set(x['axioms'])<={'propext','Classical.choice','Quot.sound'} for x in j['axioms'])
    return dict(module=m,receipt_sha256=sha(rp),seconds=j['seconds'],compiler_wall_seconds=j['compiler_wall_seconds'],axiom_reports=len(j['axioms']))
save();count=0
try:
    for m in plan['module_order']:
        assert sha(__file__)==state['driver_sha256'] and sha(H/'scripts/check_full_replay.py')==state['checker_sha256']
        item=valid(m)
        if item is None:
            if a.limit is not None and count>=a.limit:
                state['status']='PASS_BOUNDED_FULL_REPLAY_PREFIX';break
            p=H/'lean'/(m.replace('.','/')+'.lean');assert sha(p)==sources[p.relative_to(H).as_posix()]
            log=H/'logs'/('full-replay-launch-'+stamp+'-'+m+'.log')
            with log.open('w',encoding='utf-8') as out:
                child=subprocess.Popen([sys.executable,'-B','-X','utf8',str(H/'scripts/check_full_replay.py'),m,'--timeout',str(a.timeout)],stdout=out,stderr=subprocess.STDOUT,cwd=R)
                state['active']=dict(module=m,pid=child.pid,log=log.relative_to(H).as_posix());save();code=child.wait()
            state['active']=None;save();assert code==0,(m,code)
            item=valid(m);assert item is not None;count+=1
        state['checked_modules'].append(item);save();print('CHECKED',len(state['checked_modules']),'/',state['total_modules'],m,flush=True)
    else:state['status']='PASS_COMPLETE_FULL_REPLAY_MODULES'
except BaseException as e:
    state['status']='STOPPED_ON_FAILED_OR_INCOMPLETE_MODULE';state['exception']=repr(e);raise
finally:
    state['finished_at']=datetime.datetime.now(datetime.timezone.utc).isoformat();save();lock.unlink()
    print(state['status'],flush=True)
