"""Bounded second encoding test, with redundant lower counters removed."""
from pathlib import Path
import ctypes,datetime,hashlib,json,os,subprocess,time
from ctypes import wintypes
H=Path(__file__).resolve().parents[1];R=H.parents[1]
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
read=lambda p:json.loads(p.read_text(encoding='utf-8-sig'))
j=read(H/'data/reduced.json');cnf=H/'work/reduced.cnf'
assert sha(cnf)==j['reduced_sha256']
exe=Path('D:/Codex/2026-10-01/it-should-have-a-property-of/work/lean-research/lean-4.19.0-windows/bin/cadical.exe')
raw=H/'work/reduced.raw.lrat';record=H/'data/search-reduced.json';stdout=H/'logs/search-reduced.stdout.txt';stderr=H/'logs/search-reduced.stderr.txt'
assert not raw.exists() and not record.exists()
command=[str(exe),'-q','--lrat','--no-binary','--seed=1',str(cnf),str(raw)]
out=dict(status='RUNNING',pid=os.getpid(),command=command,solver_sha256=sha(exe),cnf_sha256=sha(cnf),reduction_sha256=sha(H/'data/reduced.json'),script_sha256=sha(Path(__file__)),started_at=datetime.datetime.now(datetime.timezone.utc).isoformat(),timeout_seconds=180)
def save():record.write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
save();start=time.monotonic()
with stdout.open('wb') as so,stderr.open('wb') as se:
 proc=subprocess.Popen(command,stdout=so,stderr=se);out['solver_pid']=proc.pid;save()
 try:
  code=proc.wait(timeout=180);text=stdout.read_text(errors='replace')
  out.update(exit_code=code,status='NATIVE_UNSAT_RENUMBERING_AND_ORIGINAL_REPLAY_PENDING' if code==20 and 's UNSATISFIABLE' in text else 'NATIVE_SAT_MODEL_CHECK_PENDING' if code==10 and 's SATISFIABLE' in text else 'FAILED')
 except subprocess.TimeoutExpired:
  proc.kill();proc.wait(timeout=15);out.update(exit_code=proc.returncode,status='TIMEOUT')
 try:
  f=[wintypes.FILETIME() for _ in range(4)]
  get=ctypes.windll.kernel32.GetProcessTimes;get.argtypes=[wintypes.HANDLE]+[ctypes.POINTER(wintypes.FILETIME)]*4;get.restype=wintypes.BOOL
  assert get(int(proc._handle),*[ctypes.byref(x) for x in f])
  secs=lambda x:((x.dwHighDateTime<<32)+x.dwLowDateTime)/1e7
  out.update(kernel_cpu_seconds=secs(f[2]),user_cpu_seconds=secs(f[3]))
 except Exception as e:out['cpu_measurement_error']=repr(e)
out.update(seconds=time.monotonic()-start,stdout_sha256=sha(stdout),stderr_sha256=sha(stderr),raw_sha256=sha(raw),raw_bytes=raw.stat().st_size,scope='Reduced input uses only original or proved clauses. A contradiction requires ID mapping, combined original-input replay and Lean completion. Timeout is inconclusive; no performance claim follows from wall time under concurrent proof jobs.')
save();print(json.dumps(out,indent=2),flush=True)
