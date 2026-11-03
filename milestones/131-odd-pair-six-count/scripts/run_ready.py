"""Wait briefly for the recorded memory gate, then launch one graph attempt."""
from pathlib import Path
import argparse,datetime,hashlib,json,os,subprocess,sys,time
H=Path(__file__).resolve().parents[1]
p=argparse.ArgumentParser()
p.add_argument('--label',default='odd-pair9-six25')
p.add_argument('--wait',type=int,default=180)
p.add_argument('--timeout',type=int,default=900)
a=p.parse_args()
assert a.wait>=0 and a.timeout>0
assert a.label.replace('-','').replace('_','').isalnum()
record=H/'data'/(a.label+'-launch.json')
assert not record.exists() and not (H/'data'/a.label).exists()
state=dict(status='WAITING_FOR_MEMORY',pid=os.getpid(),
 started_at=datetime.datetime.now(datetime.timezone.utc).isoformat(),
 script_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
 required_bytes=3*1024**3,observations=[])
def save():record.write_text(json.dumps(state,indent=2)+'\n',encoding='utf-8')
save();start=time.monotonic()
while True:
 free=int(subprocess.check_output(['powershell','-NoProfile','-Command',
  '[long](Get-CimInstance Win32_OperatingSystem).FreePhysicalMemory*1024'],text=True).strip())
 state['observations'].append(dict(seconds=time.monotonic()-start,free_bytes=free));save()
 if free>=state['required_bytes']:break
 if time.monotonic()-start>=a.wait:
  state['status']='NOT_STARTED_MEMORY_GATE';save();print(state['status']);sys.exit(0)
 time.sleep(3)
command=[sys.executable,'-B','-X','utf8',str(H/'scripts/evaluate_graph.py'),
 '--label',a.label,'--timeout',str(a.timeout)]
state.update(status='LAUNCHING',command=command);save()
child=subprocess.Popen(command,cwd=H.parents[1]);state['child_pid']=child.pid;save()
code=child.wait()
result=H/'data'/a.label/'run-status.json'
state.update(status='RETURNED',exit_code=code,elapsed_seconds=time.monotonic()-start,
 evaluator_status=json.loads(result.read_text())['status'] if result.exists() else 'NO_RECORD')
save();print(json.dumps(dict(status=state['status'],evaluator_status=state['evaluator_status'],exit_code=code)))
sys.exit(code)
