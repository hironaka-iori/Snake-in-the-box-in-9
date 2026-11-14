from pathlib import Path
import datetime,json,os,subprocess,sys,time
H=Path(__file__).resolve().parents[1];planpath=H/'data'/(sys.argv[1] if len(sys.argv)>1 else 'batch-plan.json');plan=json.loads(planpath.read_bytes());lock=H/'data/replay-batch.lock';assert not lock.exists()
start=time.monotonic();lock.write_text(str(os.getpid())+'\n');state=dict(status='RUNNING',pid=os.getpid(),total=len(plan['module_order']),completed=0,current=None)
def save():
 state['utc']=datetime.datetime.now(datetime.timezone.utc).isoformat();state['seconds']=time.monotonic()-start
 (H/'data/batch-progress.json').write_text(json.dumps(state,indent=2)+'\n')
try:
 with (H/'logs/batch-driver.log').open('a',encoding='utf-8') as log:
  for module in plan['module_order']:
   state['current']=module;save()
   commands=[]
   if not (H/'data'/(module+'-audit.json')).exists():commands.append([sys.executable,'-B','-X','utf8',str(H/'scripts/prepare_proof.py'),module])
   commands.append([sys.executable,'-B','-X','utf8',str(H/'scripts/check_core.py'),module,'--timeout','60'])
   for command in commands:
    p=subprocess.run(command,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True,encoding='utf-8');log.write(p.stdout);log.flush()
    if p.returncode:
     state['status']='STOPPED';state['exit_code']=p.returncode;state['last_output']=p.stdout;save();print('STOPPED',module,p.stdout[-900:],flush=True);raise SystemExit(p.returncode)
   state['completed']+=1;save()
   print('ACCEPTED',state['completed'],'/',state['total'],module,flush=True)
  state['status']='COMPLETE';state['current']=None;save()
finally:
 lock.unlink()
