"""Bounded native LP run with preserved resource observations."""
from pathlib import Path
import ctypes,hashlib,json,os,subprocess,sys,time
from native_resources import snapshot,kernel,psapi,PROCESS_MEMORY_COUNTERS_EX
H=Path(__file__).resolve().parents[1];R=H.parents[1]
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def save(p,x):p.write_text(json.dumps(x,indent=2)+'\n',encoding='utf-8')
def private(pid):
    h=kernel.OpenProcess(0x1000,False,pid)
    if not h:return None
    try:
        c=PROCESS_MEMORY_COUNTERS_EX();c.cb=ctypes.sizeof(c)
        if not psapi.GetProcessMemoryInfo(h,ctypes.byref(c),c.cb):return None
        return int(c.PrivateUsage)
    finally:kernel.CloseHandle(h)
assert not (R/'work/fullgraph-active.lock').exists()
lock=H/'data/forest-search.lock';receipt=H/'data/flow-long-execution.json'
assert not lock.exists() and not receipt.exists()
observations=[];deadline=time.monotonic()+55
while True:
    gate=snapshot();observations.append(gate)
    if not gate['errors'] and not gate['processes'] and gate['free_bytes']>=1024**3:break
    if time.monotonic()>=deadline:break
    time.sleep(1)
assert not gate['errors'] and not gate['processes'] and gate['free_bytes']>=1024**3,gate
pins={os.path.relpath(p,H):sha(p) for p in [Path(__file__),H/'scripts/flow_long.py',H/'scripts/native_resources.py',H/'data/long-0/model.json',H/'data/long-78/model.json']}
env=os.environ.copy();limits={k:'1' for k in ['OPENBLAS_NUM_THREADS','OMP_NUM_THREADS','MKL_NUM_THREADS','NUMEXPR_NUM_THREADS']};env.update(limits)
cmd=[sys.executable,'-B','-X','utf8',str(H/'scripts/flow_long.py')]
record={'status':'RUNNING','command':cmd,'pins':pins,'thread_environment':limits,'resource_gate':gate,'startup_observations':observations,'resource_samples':[]}
lock.write_text(str(os.getpid())+'\n');start=time.monotonic();stop=None
try:
    with (H/'logs/flow-long-stdout.log').open('wb') as out,(H/'logs/flow-long-stderr.log').open('wb') as err:
        child=subprocess.Popen(cmd,cwd=R,env=env,stdout=out,stderr=err);record['pid']=child.pid;save(receipt,record)
        try:
            while child.poll() is None:
                s=snapshot();memory=private(child.pid)
                record['resource_samples'].append({'free_bytes':s['free_bytes'],'private_bytes':memory,'errors':s['errors'],'lean_processes':s['processes']})
                if s['errors'] or s['processes']:stop='RESOURCE_QUERY_OR_LEAN_PROCESS'
                elif s['free_bytes']<768*1024**2:stop='LOW_FREE_MEMORY'
                elif memory is None and child.poll() is None:stop='PROCESS_MEMORY_UNAVAILABLE'
                elif memory is not None and memory>256*1024**2:stop='MEMORY_LIMIT'
                elif time.monotonic()-start>240:stop='WALL_TIMEOUT'
                if stop:child.terminate();break
                time.sleep(.1)
            code=child.wait(timeout=30)
        finally:
            if child.poll() is None:child.terminate();child.wait(timeout=30)
    assert all(sha(H/n)==v for n,v in pins.items())
    record.update(status='ACCEPTED_NATIVE_RESULT' if code==0 and stop is None else 'INTERRUPTED',exit_code=code,stop_reason=stop,
        seconds=time.monotonic()-start,stdout_sha256=sha(H/'logs/flow-long-stdout.log'),stderr_sha256=sha(H/'logs/flow-long-stderr.log'))
    if record['status']=='ACCEPTED_NATIVE_RESULT':record['summary_sha256']=sha(H/'data/flow-long-summary.json')
    save(receipt,record);print(json.dumps({k:v for k,v in record.items() if k not in ['resource_samples','pins','startup_observations']}),flush=True)
finally:lock.unlink()
