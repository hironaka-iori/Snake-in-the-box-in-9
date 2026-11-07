"""Reuse the archived cap13 CNF and add two Lean-justified closing units."""
from pathlib import Path
import gzip,json,hashlib,subprocess,os,time,gc
import native_resources as nr
H=Path(__file__).resolve().parents[1];R=H.parents[1];old=R/'milestones/180-share14-certificates'
def sha(p):
 h=hashlib.sha256()
 with Path(p).open('rb') as f:
  for b in iter(lambda:f.read(1048576),b''):h.update(b)
 return h.hexdigest()
def mem(pid):
 h=nr.kernel.OpenProcess(0x1000,False,pid)
 if not h:return 0
 try:
  v=nr.PROCESS_MEMORY_COUNTERS_EX();v.cb=nr.ctypes.sizeof(v)
  assert nr.psapi.GetProcessMemoryInfo(h,nr.ctypes.byref(v),v.cb)
  return int(v.PrivateUsage)
 finally:nr.kernel.CloseHandle(h)
s=nr.snapshot();assert not s['errors'] and not s['processes'] and s['free_bytes']>=1024**3,s
meta=json.loads((old/'data/012301.json').read_text());source=old/'certificates/012301.cnf.gz'
assert sha(source)==meta['artifacts'][source.name]
meaning=json.loads(gzip.decompress((old/'certificates/012301.meanings.json.gz').read_bytes()))['meaning']
units=[-int(k) for k,v in meaning.items() if v[0]=='p' and v[1] in [4,8]];assert len(units)==2
del meaning;gc.collect()
cache=H/'cache/stream14';cache.mkdir(parents=True);cnf=cache/'input.cnf';raw=cache/'raw.lrat';ih=hashlib.sha256()
with gzip.open(source,'rb') as src,cnf.open('wb') as dst:
 header=src.readline();ih.update(header);_,_,nv,nc=header.split();nv=int(nv);nc=int(nc)
 dst.write(f'p cnf {nv} {nc+2}\n'.encode())
 for line in src:ih.update(line);dst.write(line)
 for u in units:dst.write(f'{u} 0\n'.encode())
assert ih.hexdigest()==meta['cnf_sha256']
exe=Path('D:/Codex/2026-10-01/it-should-have-a-property-of/work/lean-research/lean-4.19.0-windows/bin/cadical.exe')
assert sha(exe)=='4fb5f4f94a3632c185ea763f7da627d40038cca38d9481952d00d04cc881c94f'
record={'status':'RUNNING','target_share':14,'cap':13,'closing_vertices':[4,8],'added_units':units,'source_sha256':ih.hexdigest(),'cnf_sha256':sha(cnf),'clauses':nc+2,'variables':nv,'initial_resources':s,'private_limit':256*1024**2,'reserve':768*1024**2,'peak_private':0,'producer_sha256':sha(__file__)}
start=time.monotonic();out=H/'logs/stream14.stdout';err=H/'logs/stream14.stderr'
with out.open('wb') as so,err.open('wb') as se:
 child=subprocess.Popen([str(exe),'-q','--lrat','--no-binary','--seed=1',str(cnf),str(raw)],stdout=so,stderr=se)
 try:
  while child.poll() is None:
   s=nr.snapshot();private=mem(os.getpid())+mem(child.pid);record['peak_private']=max(record['peak_private'],private)
   if s['errors'] or s['processes'] or s['free_bytes']<768*1024**2 or private>256*1024**2 or time.monotonic()-start>90 or (raw.exists() and raw.stat().st_size>128*1024**2):
    record['status']='BOUNDED_STOP';child.terminate();break
   time.sleep(.25)
  code=child.wait(timeout=15)
 finally:
  if child.poll() is None:child.terminate();child.wait(timeout=15)
record.update(exit_code=code,seconds=time.monotonic()-start,raw_sha256=sha(raw) if raw.exists() else None,raw_bytes=raw.stat().st_size if raw.exists() else 0)
if record['status']=='RUNNING':record['status']='UNSAT_NATIVE_REPLAY_PENDING' if code==20 and b's UNSATISFIABLE' in out.read_bytes() else 'SAT_NATIVE' if code==10 else 'UNRESOLVED'
import shutil
for name,path in [('012301-closed.cnf.gz',cnf),('012301-closed.lrat.gz',raw)]:
 if path.exists():
  with path.open('rb') as src,gzip.open(H/'certificates'/name,'wb') as dst:shutil.copyfileobj(src,dst)
record['artifacts']={p.name:sha(p) for p in (H/'certificates').glob('012301-closed.*')}
(H/'data/stream14.json').write_text(json.dumps(record,indent=2)+'\n')
print(record['status'],round(record['seconds'],2),record['raw_bytes'],flush=True)
