"""Resume the concrete total-count Lean proof in dependency order."""
from pathlib import Path
import argparse,datetime,hashlib,json,os,re,subprocess,sys,time
HERE=Path(__file__).resolve().parents[1]
read=lambda p:json.loads(p.read_text(encoding='utf-8-sig'))
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
p=argparse.ArgumentParser();p.add_argument('--limit',type=int);p.add_argument('--timeout',type=int,default=180);args=p.parse_args()
planpath=HERE/'data/total-plan.json';plan=read(planpath)
assert plan['status']=='NATIVE_EXPORT_SIMULATED_LEAN_PENDING'
replay=read(HERE/'data/replay-core1.json');assert replay['status']=='NATIVE_REFINED_CONTRADICTION_REPLAYED_LEAN_PENDING'
assert plan['selection']['choice']=='core1' and plan['selection']['trim_sha256']==replay['trim_sha256']
modules=set(plan['modules'])|{'ActualTotal115'}
sources={m:HERE/'lean'/(m.replace('.','/')+'.lean') for m in modules}
hashes={m:sha(f) for m,f in sources.items()}
ordered=[];visiting=set();seen=set()
def visit(m):
    if m in seen:return
    assert m not in visiting;visiting.add(m)
    for dep in re.findall(r'^import ([\w.]+)$',sources[m].read_text(encoding='utf-8'),re.M):
        if dep in modules:visit(dep)
    visiting.remove(m);seen.add(m);ordered.append(m)
visit('ActualTotal115');assert seen==modules
run=str(time.time_ns());runpath=HERE/'logs'/('batch-'+run+'.json');progress=HERE/'data/batch-progress.json';lock=HERE/'data/batch.lock'
with lock.open('x') as f:json.dump(dict(pid=os.getpid(),record=str(runpath)),f)
state=dict(status='RUNNING',pid=os.getpid(),started_at=datetime.datetime.now(datetime.timezone.utc).isoformat(),
    plan_sha256=sha(planpath),driver_sha256=sha(Path(__file__)),checker_sha256=sha(HERE/'scripts/check_modules.py'),
    total_modules=len(ordered),checked_modules=[],active=None,scope='Concrete total-count semantics, full contradiction replay and final actual-snake theorem; no improved global upper bound follows from this batch alone.')
def save():
    state['updated_at']=datetime.datetime.now(datetime.timezone.utc).isoformat()
    content=json.dumps(state,indent=2)+'\n';runpath.write_text(content,encoding='utf-8');progress.write_text(content,encoding='utf-8')
def checked(m):
    rp=HERE/'data'/(m+'-audit.json')
    if not rp.exists():return None
    r=read(rp);assert r['status']=='PASS_TOTAL_COUNT_MODULE' and r['exit_code']==0 and not r['timeout']
    assert sha(sources[m])==hashes[m]==r['source_sha256']
    assert sha(HERE/'build'/(m.replace('.','/')+'.olean'))==r['olean_sha256'] and sha(HERE/r['log'])==r['log_sha256']
    assert sha(HERE/r['source_snapshot'])==r['source_sha256']
    for d,digest in r['dependencies'].items():assert sha(Path(d))==digest,d
    for a in r['theorem_audits']:assert set(a['axioms'])<={'propext','Classical.choice','Quot.sound'}
    return dict(module=m,receipt_sha256=sha(rp),seconds=r['seconds'],theorem_audits=len(r['theorem_audits']))
save();new=0
try:
    for m in ordered:
        receipt=checked(m)
        if receipt is None:
            if args.limit is not None and new>=args.limit:
                state['status']='PASS_BOUNDED_PREFIX';break
            assert sha(planpath)==state['plan_sha256'] and sha(Path(__file__))==state['driver_sha256']
            assert sha(HERE/'scripts/check_modules.py')==state['checker_sha256']
            log=HERE/'logs'/('batch-'+run+'-'+m+'.log')
            command=[sys.executable,'-B','-X','utf8',str(HERE/'scripts/check_modules.py'),m,'--timeout',str(args.timeout)]
            with log.open('w',encoding='utf-8') as out:
                proc=subprocess.Popen(command,stdout=out,stderr=subprocess.STDOUT)
                state['active']=dict(module=m,pid=proc.pid,log=log.relative_to(HERE).as_posix());save()
                code=proc.wait()
            state['active']=None;save();assert code==0,('Checker stopped',m,code,str(log))
            receipt=checked(m);assert receipt is not None;new+=1
        state['checked_modules'].append(receipt);save();print('CHECKED',len(state['checked_modules']),'/',len(ordered),m,flush=True)
    else:state['status']='PASS_COMPLETE_TOTAL_COUNT_PROOF'
except BaseException as exc:
    state.update(status='STOPPED',exception=repr(exc));raise
finally:
    state['finished_at']=datetime.datetime.now(datetime.timezone.utc).isoformat();save()
    if state['active'] is None:lock.unlink()
