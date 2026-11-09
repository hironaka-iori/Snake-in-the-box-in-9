"""One sequential proof worker; bounded resource waits never weaken a guard."""
from pathlib import Path
import sys,json,time,subprocess,datetime,os,hashlib
H=Path('E:/Snake-in-a-box/milestones/186-structural-interpretation')
sys.path.insert(0,str(H/'scripts'))
import native_resources as nr
order=json.loads((H/'data/current-order.json').read_text())
deadline=time.monotonic()+600
runid=str(time.time_ns()); record=H/'data'/('run-'+runid+'.json')
state={'status':'RUNNING','pid':os.getpid(),'started_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'checks':[],'resource_waits':[]}
def save():
 record.write_text(json.dumps(state,indent=2)+'\n')
save()
for name in order:
 if (H/'data'/(name+'-audit.json')).exists():continue
 while True:
  if time.monotonic()>=deadline:
   state['status']='BOUNDED_STOP';save();print('BOUNDED_STOP',name,flush=True);raise SystemExit(0)
  snap=nr.snapshot()
  if not snap['errors'] and not snap['processes'] and snap['free_bytes']>=1024**3:break
  state['resource_waits'].append({'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'snapshot':snap,'next_module':name})
  save();print('WAIT_RESOURCE',name,snap['free_bytes'],flush=True);time.sleep(10)
 state['current_module']=name;save()
 oldlogs=set((H/'logs').glob(name+'-*'))
 r=subprocess.run([sys.executable,'-B','-X','utf8',str(H/'scripts/check_core.py'),name],cwd=H.parents[1],capture_output=True,text=True)
 state['checks'].append({'module':name,'exit_code':r.returncode,'stdout':r.stdout,'stderr':r.stderr})
 print(r.stdout or r.stderr,flush=True)
 if r.returncode:
  if set((H/'logs').glob(name+'-*'))==oldlogs:
   state['status']='STARTUP_STOP'
  else:state['status']='CHECK_STOP'
  save();raise SystemExit(r.returncode)
 save()
state['status']='PASS_ALL_CURRENT_MODULES'
state['finished_utc']=datetime.datetime.now(datetime.timezone.utc).isoformat()
save();print(state['status'],flush=True)

