from pathlib import Path
import sys,os,time,subprocess,json,hashlib,datetime
from native_guard_v5 import snapshot
h=Path(__file__).resolve().parents[1];r=h.parents[1];lock=r/'work/fullgraph-active.lock'
s=snapshot({os.getpid()});assert not s['errors'] and not s['lean_processes'] and not s['graph_processes'] and s['free_bytes']>=2*1024**3,s
record={'started_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'initial':s,'script_sha256':hashlib.sha256((h/'scripts/retune.py').read_bytes()).hexdigest(),'peak_private':0,'status':'RUNNING'}
with lock.open('x') as f:json.dump({'round':177,'parent':os.getpid()},f)
child=None
try:
 with (h/'data/stdout.log').open('w',encoding='utf-8') as out,(h/'data/stderr.log').open('w',encoding='utf-8') as err:
  child=subprocess.Popen([sys.executable,'-B','-X','utf8',str(h/'scripts/retune.py')],cwd=r,stdout=out,stderr=err)
  start=time.monotonic()
  while child.poll() is None:
   s=snapshot({os.getpid(),child.pid});private=sum(x['private_bytes'] for x in s['owned_memory']);record['peak_private']=max(record['peak_private'],private)
   if s['errors'] or s['lean_processes'] or s['free_bytes']<768*1024**2 or private>1024**3 or time.monotonic()-start>600:
    record.update(status='RESOURCE_STOP',last=s);child.terminate();break
   time.sleep(1)
  code=child.wait(timeout=15);record['exit_code']=code
  if record['status']=='RUNNING':record['status']='PASS' if code==0 else 'FAILED'
finally:
 if child is not None and child.poll() is None:child.terminate();child.wait(timeout=15)
 record['finished_utc']=datetime.datetime.now(datetime.timezone.utc).isoformat()
 (h/'data/graph-run.json').write_text(json.dumps(record,indent=2)+'\n',encoding='utf-8')
 if lock.exists() and json.loads(lock.read_text()).get('parent')==os.getpid():lock.unlink()
print(record['status'],record.get('exit_code'),record['peak_private'])
