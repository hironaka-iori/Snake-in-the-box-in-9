"""Resume the exact selected core interpretation, with one bounded checker at a time."""
from pathlib import Path
import argparse,datetime,hashlib,json,os,subprocess,sys,time
H=Path(__file__).resolve().parents[1];R=H.parents[1]
read=lambda p:json.loads(p.read_text(encoding='utf-8-sig'))
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
ap=argparse.ArgumentParser();ap.add_argument('--limit',type=int);ap.add_argument('--timeout',type=int,default=180);a=ap.parse_args()
planpath=H/'data/semantic-plan.json';plan=read(planpath)
assert plan['status']=='PREPARED_EXACT_012301_CORE_INTERPRETATION_LEAN_PENDING'
sources={x['path']:x['sha256'] for x in plan['artifacts']}
assert a.limit is None or a.limit>0
assert a.timeout>0
lock=H/'data/semantic-batch.lock';stamp=str(time.time_ns())
record=H/'logs'/('semantic-batch-'+stamp+'.json');progress=H/'data/semantic-progress.json'
with lock.open('x') as f:json.dump(dict(pid=os.getpid(),record=record.relative_to(H).as_posix()),f)
state=dict(status='RUNNING',pid=os.getpid(),started_at=datetime.datetime.now(datetime.timezone.utc).isoformat(),
    total_modules=len(plan['module_order']),checked_modules=[],active=None,plan_sha256=sha(planpath),
    driver_sha256=sha(__file__),checker_sha256=sha(H/'scripts/check_semantic.py'),
    requested_new_module_limit=a.limit,
    scope='Only exact core clause-interpretation modules. This does not complete the contradiction or actual-snake share theorem.')
def save():
    state['updated_at']=datetime.datetime.now(datetime.timezone.utc).isoformat()
    s=json.dumps(state,indent=2)+'\n';record.write_text(s);progress.write_text(s)
def valid(m):
    rp=H/'data'/(m+'-audit.json')
    if not rp.exists():return None
    j=read(rp);assert j['status']=='PASS' and j['exit_code']==0 and j['stop_reason'] is None
    p=H/'lean'/(m.replace('.','/')+'.lean')
    assert sha(p)==j['source_sha256']==sources[p.relative_to(H).as_posix()]
    assert sha(j['object'])==j['olean_sha256'] and sha(j['log'])==j['log_sha256']
    for p,d in j['dependencies'].items():assert sha(Path(p) if Path(p).is_absolute() else R/p)==d
    assert all(set(x['axioms'])<={'propext','Classical.choice','Quot.sound'} for x in j['axioms'])
    return dict(module=m,receipt_sha256=sha(rp),seconds=j['seconds'],axiom_reports=len(j['axioms']))
save();count=0
try:
    for m in plan['module_order']:
        item=valid(m)
        if item is None:
            if a.limit is not None and count>=a.limit:
                state['status']='PASS_BOUNDED_SEMANTIC_PREFIX';break
            p=H/'lean'/(m.replace('.','/')+'.lean');assert sha(p)==sources[p.relative_to(H).as_posix()]
            log=H/'logs'/('semantic-launch-'+stamp+'-'+m+'.log')
            with log.open('w') as out:
                child=subprocess.Popen([sys.executable,'-B','-X','utf8',str(H/'scripts/check_semantic.py'),m,'--timeout',str(a.timeout)],stdout=out,stderr=subprocess.STDOUT,cwd=R)
                state['active']=dict(module=m,pid=child.pid,log=log.relative_to(H).as_posix());save();code=child.wait()
            state['active']=None;save();assert code==0,(m,code)
            item=valid(m);assert item is not None;count+=1
        state['checked_modules'].append(item);save();print('CHECKED',len(state['checked_modules']),'/',state['total_modules'],m,flush=True)
    else:state['status']='PASS_COMPLETE_CORE_CLAUSE_CHECKS'
except BaseException as e:
    state['status']='STOPPED_ON_FAILED_OR_INCOMPLETE_MODULE';state['exception']=repr(e);raise
finally:
    state['finished_at']=datetime.datetime.now(datetime.timezone.utc).isoformat();save();lock.unlink()
    print(state['status'],flush=True)
