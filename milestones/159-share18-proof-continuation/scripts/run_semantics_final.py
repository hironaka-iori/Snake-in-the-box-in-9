"""One compiler at a time; reuse accepted modules, stop at the first failure."""
from pathlib import Path
import argparse,json,os,subprocess,sys,time
H=Path(__file__).resolve().parents[1];R=H.parents[1]
ap=argparse.ArgumentParser();ap.add_argument('--limit',type=int);a=ap.parse_args()
plan=json.loads((H/'data/semantic-final-execution.json').read_text())
lock=H/'data/semantic-final-batch.lock'
with lock.open('x') as f:json.dump({'pid':os.getpid()},f)
state=dict(status='RUNNING',pid=os.getpid(),checked=[],active=None,new_modules=0,total_new_modules=len(plan['new_module_order']))
record=H/'logs'/('semantic-final-batch-'+str(time.time_ns())+'.json');record.parent.mkdir(parents=True,exist_ok=True)
def save():
    b=json.dumps(state,indent=2)+'\n';record.write_text(b,encoding='utf-8');(H/'data/semantic-final-progress.json').write_text(b,encoding='utf-8')
try:
    save()
    for m in plan['new_module_order']:
        existed=(H/'data'/(m+'-audit.json')).exists()
        if not existed and a.limit is not None and state['new_modules']>=a.limit:
            state['status']='PASS_BOUNDED_SEMANTIC_PREFIX';break
        with (record.parent/(record.stem+'-'+m+'.log')).open('w',encoding='utf-8') as log:
            child=subprocess.Popen([sys.executable,'-B','-X','utf8',str(H/'scripts/check_semantic_final.py'),m],cwd=R,stdout=log,stderr=subprocess.STDOUT)
            state['active']={'module':m,'pid':child.pid};save();code=child.wait()
        state['active']=None
        if code:
            state['status']='STOPPED_ON_FAILED_OR_INCOMPLETE_MODULE';state['failed_module']=m;save();raise SystemExit(code)
        state['checked'].append(m);state['new_modules']+=not existed;save();print('CHECKED',len(state['checked']),m,flush=True)
    else:state['status']='PASS_COMPLETE_SEMANTIC_MODULES'
finally:
    save();lock.unlink();print(state['status'],flush=True)
