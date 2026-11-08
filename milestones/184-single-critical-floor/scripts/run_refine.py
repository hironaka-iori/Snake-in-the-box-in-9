from pathlib import Path
import sys,os,json,time,subprocess,hashlib,datetime
from native_guard_v5 import snapshot
H=Path(__file__).resolve().parents[1];R=H.parents[1]
lock=R/'work/fullgraph-active.lock'
s=snapshot({os.getpid()})
# This batch-based producer replaces full graph-sized intermediate arrays.
# Its private-memory cap is half the previous producer's, and startup
# requires that cap plus the unchanged 768 MiB free-memory reserve.
cap=512*1024**2;reserve=768*1024**2
record={'status':'STARTING','started_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'initial':s,'private_cap':cap,'free_reserve':reserve,'startup_requirement':cap+reserve,'peak_private':0,'producer_sha256':hashlib.sha256((H/'scripts/refine_uniform.py').read_bytes()).hexdigest()}
assert not s['errors'] and not s['lean_processes'] and not s['graph_processes'] and s['free_bytes']>=cap+reserve,s
with lock.open('x') as f:json.dump({'round':184,'parent':os.getpid()},f)
child=None
try:
    with (H/'data/refine-stdout.log').open('w') as out,(H/'data/refine-stderr.log').open('w') as err:
        child=subprocess.Popen([sys.executable,'-B','-X','utf8',str(H/'scripts/refine_uniform.py')],cwd=R,stdout=out,stderr=err)
        record.update(status='RUNNING',child_pid=child.pid);start=time.monotonic()
        while child.poll() is None:
            s=snapshot({os.getpid(),child.pid});private=sum(x['private_bytes'] for x in s['owned_memory']);record['peak_private']=max(record['peak_private'],private)
            if s['errors'] or s['lean_processes'] or private>cap or s['free_bytes']<reserve or time.monotonic()-start>540:
                record.update(status='RESOURCE_STOP',last=s);child.terminate();break
            time.sleep(1)
        code=child.wait(timeout=15);record['exit_code']=code
        if record['status']=='RUNNING':record['status']='PASS' if code==0 else 'FAILED'
finally:
    if child is not None and child.poll() is None:child.terminate();child.wait(timeout=15)
    record['finished_utc']=datetime.datetime.now(datetime.timezone.utc).isoformat()
    (H/'data/refine-worker.json').write_text(json.dumps(record,indent=2)+'\n')
    if lock.exists() and json.loads(lock.read_text()).get('parent')==os.getpid():lock.unlink()
print(record['status'],record.get('exit_code'),'peak_private',record['peak_private'])
