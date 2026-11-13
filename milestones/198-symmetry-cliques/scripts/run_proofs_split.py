from pathlib import Path
import json,subprocess,sys,time
from native_resources import snapshot
H=Path(__file__).resolve().parents[1];R=H.parents[1]
modules=['EndpointData198', 'EndpointVertex198_0', 'EndpointVertex198_1', 'EndpointVertex198_2', 'EndpointVertex198_3', 'EndpointVertex198_4', 'EndpointVertex198_5', 'EndpointVertex198_6', 'EndpointVertex198_7', 'EndpointFacts198', 'EndpointChunk198_0_0', 'EndpointChunk198_0_1', 'EndpointChunk198_0_2', 'EndpointChunk198_0_3', 'EndpointChunk198_0_4', 'EndpointChunk198_0_5', 'EndpointChunk198_0_6', 'EndpointChunk198_0_7', 'EndpointStep198_0', 'EndpointChunk198_1_0', 'EndpointChunk198_1_1', 'EndpointChunk198_1_2', 'EndpointChunk198_1_3', 'EndpointChunk198_1_4', 'EndpointChunk198_1_5', 'EndpointChunk198_1_6', 'EndpointChunk198_1_7', 'EndpointStep198_1', 'EndpointChunk198_2_0', 'EndpointChunk198_2_1', 'EndpointChunk198_2_2', 'EndpointChunk198_2_3', 'EndpointChunk198_2_4', 'EndpointChunk198_2_5', 'EndpointChunk198_2_6', 'EndpointChunk198_2_7', 'EndpointStep198_2', 'EndpointChunk198_3_0', 'EndpointChunk198_3_1', 'EndpointChunk198_3_2', 'EndpointChunk198_3_3', 'EndpointChunk198_3_4', 'EndpointChunk198_3_5', 'EndpointChunk198_3_6', 'EndpointChunk198_3_7', 'EndpointStep198_3', 'EndpointChunk198_4_0', 'EndpointChunk198_4_1', 'EndpointChunk198_4_2', 'EndpointChunk198_4_3', 'EndpointChunk198_4_4', 'EndpointChunk198_4_5', 'EndpointChunk198_4_6', 'EndpointChunk198_4_7', 'EndpointStep198_4', 'EndpointChunk198_5_0', 'EndpointChunk198_5_1', 'EndpointChunk198_5_2', 'EndpointChunk198_5_3', 'EndpointChunk198_5_4', 'EndpointChunk198_5_5', 'EndpointChunk198_5_6', 'EndpointChunk198_5_7', 'EndpointStep198_5', 'EndpointTransport198', 'PairRows198_0', 'PairRows198_1', 'PairRows198_2', 'PairRows198_3', 'Cliques198']
receipt=H/'data/proof-batch-split.json';assert not receipt.exists()
start=time.monotonic();rows=[];waits=[];state='RUNNING'
for module in modules:
 while True:
  s=snapshot()
  if not s['errors'] and not s['processes'] and s['free_bytes']>=1024*1024**2:break
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
