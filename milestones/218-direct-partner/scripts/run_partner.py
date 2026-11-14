"""Run the two native partner queries sequentially with recorded resource limits."""
from pathlib import Path
import argparse, ctypes, hashlib, json, os, subprocess, sys, time
from native_resources import snapshot, kernel, psapi, PROCESS_MEMORY_COUNTERS_EX

H = Path(__file__).resolve().parents[1]
R = H.parents[1]
def sha(p): return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def save(p, obj):
    q = p.with_name(p.name + '.tmp')
    q.write_text(json.dumps(obj, indent=2) + '\n', encoding='utf-8')
    os.replace(q, p)
def private_bytes(pid):
    handle = kernel.OpenProcess(0x1000, False, pid)
    if not handle: return None
    try:
        c = PROCESS_MEMORY_COUNTERS_EX(); c.cb = ctypes.sizeof(c)
        if not psapi.GetProcessMemoryInfo(handle, ctypes.byref(c), c.cb): return None
        return int(c.PrivateUsage)
    finally:
        kernel.CloseHandle(handle)

ap = argparse.ArgumentParser()
ap.add_argument('--roots', type=int, nargs='+', default=[0,78])
ap.add_argument('--seconds', type=float, default=240)
a = ap.parse_args()
assert a.seconds > 0 and len(set(a.roots)) == len(a.roots) and set(a.roots) <= {0,78}
assert not (R / 'work/fullgraph-active.lock').exists()
lock = H / 'data/partner-search.lock'
assert not lock.exists()
lock.write_text(str(os.getpid()) + '\n')
receipts = []
try:
    for root in a.roots:
        F = H / 'data/threads1' / ('root-' + str(root))
        assert not F.exists(), 'Preserve the existing query; never restart a live or completed invocation.'
        observations = []; deadline = time.monotonic() + 55
        while True:
            gate = snapshot(); observations.append(gate)
            if not gate['errors'] and not gate['processes'] and gate['free_bytes'] >= 1024**3: break
            if time.monotonic() >= deadline: break
            time.sleep(1)
        if gate['errors'] or gate['processes'] or gate['free_bytes'] < 1024**3:
            save(H / 'logs' / ('startup-' + str(time.time_ns()) + '.json'), observations)
            print('STARTUP_WAIT', root, flush=True); break
        F.mkdir(parents=True)
        pins = {str(p.relative_to(H)):sha(p) for p in [Path(__file__), H/'scripts/partner_search.py',
                H/'scripts/native_resources.py', H/'data/seed98.json', H/'data/complement-graph.json']}
        cmd = [sys.executable, '-B', '-X', 'utf8', str(H/'scripts/partner_search.py'),
               '--root', str(root), '--seconds', str(a.seconds), '--output-dir', str(F)]
        env = os.environ.copy()
        thread_limits = {k:'1' for k in ['OPENBLAS_NUM_THREADS','OMP_NUM_THREADS','MKL_NUM_THREADS','NUMEXPR_NUM_THREADS']}
        env.update(thread_limits)
        receipt = {'thread_environment':thread_limits, 'status':'RUNNING', 'root':root, 'command':cmd, 'pins':pins, 'resource_gate':gate,
                   'startup_observations':observations, 'resource_samples':[]}
        started = time.monotonic(); stop = None
        with (F/'stdout.log').open('wb') as out, (F/'stderr.log').open('wb') as err:
            child = subprocess.Popen(cmd, cwd=R, env=env, stdout=out, stderr=err)
            receipt['pid'] = child.pid; save(F/'execution.json', receipt)
            try:
                while child.poll() is None:
                    sample = snapshot(); private = private_bytes(child.pid)
                    receipt['resource_samples'].append({'free_bytes':sample['free_bytes'], 'private_bytes':private,
                                                       'errors':sample['errors'], 'lean_processes':sample['processes']})
                    if sample['errors'] or sample['processes']: stop = 'RESOURCE_QUERY_OR_LEAN_PROCESS'
                    elif sample['free_bytes'] < 768*1024**2: stop = 'LOW_FREE_MEMORY'
                    elif private is None and child.poll() is None: stop = 'PROCESS_MEMORY_UNAVAILABLE'
                    elif private is not None and private > 256*1024**2: stop = 'MEMORY_LIMIT'
                    elif time.monotonic() - started > a.seconds + 20: stop = 'WALL_TIMEOUT'
                    if stop:
                        child.terminate(); break
                    time.sleep(.25)
                code = child.wait(timeout=30)
            finally:
                if child.poll() is None: child.terminate(); child.wait(timeout=30)
        assert all(sha(H/name) == digest for name,digest in pins.items())
        receipt.update(status='ACCEPTED_NATIVE_RESULT' if code == 0 and stop is None else 'INTERRUPTED',
                       exit_code=code, stop_reason=stop, wall_seconds=time.monotonic()-started,
                       stdout_sha256=sha(F/'stdout.log'), stderr_sha256=sha(F/'stderr.log'))
        if receipt['status'] == 'ACCEPTED_NATIVE_RESULT':
            result = json.loads((F/'result.json').read_bytes())
            assert result['root'] == root and result['target_edges'] == 93
            receipt.update(result_sha256=sha(F/'result.json'), solver_status=result['status'])
        save(F/'execution.json', receipt)
        receipts.append({'root':root, 'receipt_sha256':sha(F/'execution.json'), 'status':receipt['status'],
                         'solver_status':receipt.get('solver_status'), 'stop_reason':stop})
        save(H/'data/threads1/batch-progress.json', {'receipts':receipts})
        print(json.dumps(receipts[-1]), flush=True)
        if receipt['status'] != 'ACCEPTED_NATIVE_RESULT' or receipt.get('solver_status') == 'FEASIBLE': break
finally:
    lock.unlink()
