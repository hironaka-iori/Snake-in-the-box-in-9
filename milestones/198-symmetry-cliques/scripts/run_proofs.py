from pathlib import Path
import json,subprocess,sys,time
from native_resources import snapshot
H=Path(__file__).resolve().parents[1];R=H.parents[1]
modules=['Cliques198']+[f'PairRows198_{i}' for i in range(4)]+['EndpointData198']+[f'EndpointStep198_{i}' for i in range(6)]+['EndpointTransport198']
receipt=H/'data/proof-batch.json';assert not receipt.exists()
start=time.monotonic();rows=[];waits=[];state='RUNNING'
for module in modules:
 while True:
  s=snapshot()
  if not s['errors'] and not s['processes'] and s['free_bytes']>=1400*1024**2:break
  waits.append(dict(module=module,elapsed=time.monotonic()-start,free_bytes=s['free_bytes'],processes=s['processes'],errors=s['errors']))
  receipt.write_text(json.dumps(dict(status='WAITING_MEMORY',module=module,rows=rows,waits=waits),indent=2)+'\n')
  if time.monotonic()-start>300:state='DEFERRED';break
  time.sleep(5)
 if state=='DEFERRED':break
 print('CHECKING',module,flush=True)
 for script in ['prepare_proof.py','check_core.py']:
  if script=='prepare_proof.py' and (H/'data'/(module+'-audit.json')).exists():continue
  r=subprocess.run([sys.executable,'-B','-X','utf8',str(H/'scripts'/script),module],cwd=R,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True)
  log=H/'logs'/(module+'-'+script+'-batch.log');log.write_text(r.stdout,encoding='utf-8');print(r.stdout,flush=True)
  if r.returncode:state='STOPPED';break
 rows.append(dict(module=module,exit_code=r.returncode))
 receipt.write_text(json.dumps(dict(status=state,module=module,rows=rows,waits=waits),indent=2)+'\n')
 if state=='STOPPED':break
if len(rows)==len(modules) and state!='STOPPED':state='COMPLETE'
receipt.write_text(json.dumps(dict(status=state,rows=rows,waits=waits,seconds=time.monotonic()-start),indent=2)+'\n')
print('BATCH',state,flush=True)
