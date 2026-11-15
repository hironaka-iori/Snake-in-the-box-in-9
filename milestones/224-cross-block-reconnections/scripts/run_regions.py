"""Run one bounded constructive query and retain its resource receipt."""
from pathlib import Path
import ctypes, hashlib, json, os, subprocess, sys, time
from native_resources import snapshot, kernel, psapi, PROCESS_MEMORY_COUNTERS_EX
H = Path(__file__).resolve().parents[1]; R = H.parents[1]
def sha(p): return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def save(p, x): p.write_text(json.dumps(x, indent=2)+'\n', encoding='utf-8')
def private(pid):
    h = kernel.OpenProcess(0x1000, False, pid)
    if not h: return None
    try:
        c = PROCESS_MEMORY_COUNTERS_EX(); c.cb = ctypes.sizeof(c)
        return int(c.PrivateUsage) if psapi.GetProcessMemoryInfo(h, ctypes.byref(c), c.cb) else None
    finally: kernel.CloseHandle(h)
args = sys.argv[1:]; tag = args[args.index('--tag')+1]
seconds = float(args[args.index('--seconds')+1])
receipt = H/'data'/(tag+'-execution.json'); lock = H/'data/forest-search.lock'
assert not receipt.exists() and not lock.exists() and not (R/'work/fullgraph-active.lock').exists()
startup=[]; deadline=time.monotonic()+55
while True:
    gate=snapshot(); startup.append(gate)
    if not gate['errors'] and not gate['processes'] and gate['free_bytes']>=1024**3: break
    if time.monotonic()>=deadline:
        save(H/'logs'/(tag+'-startup.json'), dict(status='STARTUP_DEFERRED', observations=startup))
        print('STARTUP_DEFERRED', flush=True); raise SystemExit(2)
    time.sleep(1)
env = os.environ.copy()
limits = {k:'1' for k in ['OPENBLAS_NUM_THREADS','OMP_NUM_THREADS','MKL_NUM_THREADS','NUMEXPR_NUM_THREADS']}
env.update(limits)
cmd = [sys.executable,'-B','-X','utf8',str(H/'scripts/joint_regions.py')]+args
pins = {str(p):sha(p) for p in [Path(__file__), H/'scripts/joint_regions.py', H/'scripts/native_resources.py', H/'data/regions.json']}
record = dict(status='RUNNING', command=cmd, pins=pins, resource_gate=gate, startup_observations=startup, thread_environment=limits, resource_samples=[])
lock.write_text(str(os.getpid())+'\n'); start=time.monotonic(); stop=None
try:
    with (H/'logs'/(tag+'-stdout.log')).open('wb') as out, (H/'logs'/(tag+'-stderr.log')).open('wb') as err:
        child=subprocess.Popen(cmd,cwd=R,env=env,stdout=out,stderr=err)
        record['pid']=child.pid; save(receipt,record)
        try:
            while child.poll() is None:
                s=snapshot(); mem=private(child.pid)
                record['resource_samples'].append(dict(free_bytes=s['free_bytes'],private_bytes=mem,errors=s['errors'],lean_processes=s['processes']))
                if s['errors'] or s['processes']: stop='RESOURCE_QUERY_OR_LEAN_PROCESS'
                elif s['free_bytes']<768*1024**2: stop='LOW_FREE_MEMORY'
                elif mem is None and child.poll() is None: stop='PROCESS_MEMORY_UNAVAILABLE'
                elif mem is not None and mem>256*1024**2: stop='MEMORY_LIMIT'
                elif time.monotonic()-start>seconds+30: stop='WALL_TIMEOUT'
                if stop: child.terminate(); break
                time.sleep(.2)
            code=child.wait(timeout=30)
        finally:
            if child.poll() is None: child.terminate(); child.wait(timeout=30)
    assert all(sha(p)==d for p,d in pins.items())
    record.update(status='ACCEPTED_NATIVE_RESULT' if code==0 and stop is None else 'INTERRUPTED',exit_code=code,stop_reason=stop,seconds=time.monotonic()-start)
    for name in ['stdout','stderr']: record[name+'_sha256']=sha(H/'logs'/(tag+'-'+name+'.log'))
    if (H/'data'/(tag+'.json')).exists(): record['result_sha256']=sha(H/'data'/(tag+'.json'))
    save(receipt,record)
    print(json.dumps({k:v for k,v in record.items() if k not in ['resource_samples','pins']}),flush=True)
finally: lock.unlink()
