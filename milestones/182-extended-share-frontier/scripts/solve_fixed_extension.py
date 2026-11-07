"""Bounded floor-15 query for the representative extension at vertex 16.

Its reduction from arbitrary extension uses the written cube-isometry argument;
the native result alone does not certify that geometric reduction in Lean.
"""
from pathlib import Path
import gc,gzip,hashlib,json,os,shutil,subprocess,time
import native_resources as nr
H=Path(__file__).resolve().parents[1]
label='012301-floor15-fixed16'

def sha(p):
 h=hashlib.sha256()
 with Path(p).open('rb') as f:
  for b in iter(lambda:f.read(1048576),b''):h.update(b)
 return h.hexdigest()

def private(pid):
 h=nr.kernel.OpenProcess(0x1000,False,pid)
 if not h:return 0
 try:
  v=nr.PROCESS_MEMORY_COUNTERS_EX();v.cb=nr.ctypes.sizeof(v)
  assert nr.psapi.GetProcessMemoryInfo(h,nr.ctypes.byref(v),v.cb)
  return int(v.PrivateUsage)
 finally:nr.kernel.CloseHandle(h)

def save(d):
 (H/'data'/(label+'.json')).write_text(json.dumps(d,indent=2)+'\n')

assert not (H/'data'/(label+'.json')).exists()
s=nr.snapshot();record={'status':'PREPARING','initial_resources':s,'producer_sha256':sha(__file__)}
if s['errors'] or s['processes'] or s['free_bytes']<1024**3:
 record['status']='NOT_STARTED_RESOURCE_GATE';save(record);print(record['status'],flush=True);raise SystemExit(0)
meta=json.loads((H/'data/012301-floor15.json').read_text())
source=H/'certificates/012301-floor15.cnf.gz'
assert sha(source)==meta['artifacts'][source.name]
sem=H.parents[1]/'milestones/180-share14-certificates/certificates/012301.meanings.json.gz'
assert sha(sem)==meta['source_semantics_sha256']
meaning=json.loads(gzip.decompress(sem.read_bytes()))['meaning']
unit=[int(k) for k,v in meaning.items() if v==['p',16]]
assert len(unit)==1
del meaning;gc.collect()
cache=H/'cache'/label;cache.mkdir(parents=True);cnf=cache/'input.cnf';raw=cache/'raw.lrat'
digest=hashlib.sha256()
with gzip.open(source,'rb') as src,cnf.open('wb') as dst:
 header=src.readline();digest.update(header);_,_,nv,nc=header.split();nv=int(nv);nc=int(nc)
 dst.write(f'p cnf {nv} {nc+1}\n'.encode())
 for line in src:digest.update(line);dst.write(line)
 dst.write(f'{unit[0]} 0\n'.encode())
assert digest.hexdigest()==meta['cnf_sha256']
exe=Path('D:/Codex/2026-10-01/it-should-have-a-property-of/work/lean-research/lean-4.19.0-windows/bin/cadical.exe')
assert sha(exe)==meta['solver_sha256']
record.update(status='RUNNING',shape='012301',cap=14,target_share=15,selected_extension=16,
              added_unit=unit[0],source_cnf_sha256=digest.hexdigest(),cnf_sha256=sha(cnf),
              variables=nv,clauses=nc+1,private_limit=256*1024**2,reserve=768*1024**2,peak_private=0)
stdout=H/'logs'/(label+'.stdout');stderr=H/'logs'/(label+'.stderr');start=time.monotonic()
command=[str(exe),'-q','--lrat','--no-binary','--seed=1',str(cnf),str(raw)]
with stdout.open('wb') as so,stderr.open('wb') as se:
 child=subprocess.Popen(command,stdout=so,stderr=se,creationflags=getattr(subprocess,'CREATE_NO_WINDOW',0))
 record.update(pid=child.pid,command=command);save(record)
 try:
  while child.poll() is None:
   s=nr.snapshot();used=private(os.getpid())+private(child.pid);record['peak_private']=max(record['peak_private'],used)
   if s['errors'] or s['processes'] or s['free_bytes']<768*1024**2 or used>256*1024**2:
    record.update(status='RESOURCE_STOP',stop_snapshot=s);child.terminate();break
   if time.monotonic()-start>90 or (raw.exists() and raw.stat().st_size>128*1024**2):
    record['status']='BOUNDED_STOP';child.terminate();break
   time.sleep(.25)
  code=child.wait(timeout=15)
 finally:
  if child.poll() is None:child.terminate();child.wait(timeout=15)
record.update(exit_code=code,seconds=time.monotonic()-start,raw_bytes=raw.stat().st_size if raw.exists() else 0,raw_sha256=sha(raw) if raw.exists() else None)
if record['status']=='RUNNING':record['status']='UNSAT_NATIVE_REPLAY_PENDING' if code==20 and b's UNSATISFIABLE' in stdout.read_bytes() else 'SAT_NATIVE' if code==10 else 'UNRESOLVED'
for name,p in [(label+'.cnf.gz',cnf),(label+'.lrat.gz',raw)]:
 if p.exists():
  with p.open('rb') as src,gzip.open(H/'certificates'/name,'wb') as dst:shutil.copyfileobj(src,dst)
record['artifacts']={p.name:sha(p) for p in (H/'certificates').glob(label+'.*')}
save(record);print(record['status'],round(record['seconds'],2),record['raw_bytes'],flush=True)
