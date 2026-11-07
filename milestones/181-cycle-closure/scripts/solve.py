"""A share15 query for012301 with its two forbidden closing vertices."""
from pathlib import Path
import sys,os,time,json,gzip,hashlib,subprocess,gc
import native_resources as nr
H=Path(__file__).resolve().parents[1];R=H.parents[1]
sys.dont_write_bytecode=True
sys.path.insert(0,str(R/'milestones/28-direct-share-certificates/scripts'))
from tagged_share import TaggedShare
import tagged_share,gen_lean_sat,wincert
EXE=Path('D:/Codex/2026-10-01/it-should-have-a-property-of/work/lean-research/lean-4.19.0-windows/bin/cadical.exe')
def sha(p):
 h=hashlib.sha256()
 with Path(p).open('rb') as f:
  for b in iter(lambda:f.read(1048576),b''):h.update(b)
 return h.hexdigest()
def save(p,j):p.write_text(json.dumps(j,indent=2)+'\n',encoding='utf-8')
def mem(pid):
 handle=nr.kernel.OpenProcess(0x1000,False,pid)
 if not handle:return 0
 try:
  value=nr.PROCESS_MEMORY_COUNTERS_EX();value.cb=nr.ctypes.sizeof(value)
  if not nr.psapi.GetProcessMemoryInfo(handle,nr.ctypes.byref(value),value.cb):raise RuntimeError('Process memory unavailable')
  return int(value.PrivateUsage)
 finally:nr.kernel.CloseHandle(handle)
assert sha(EXE)=='4fb5f4f94a3632c185ea763f7da627d40038cca38d9481952d00d04cc881c94f'
initial=nr.snapshot();assert not initial['processes'] and not initial['errors'] and initial['free_bytes']>=1610612736,initial
pins={str(p):sha(p) for p in [EXE,Path(tagged_share.__file__),Path(gen_lean_sat.__file__),Path(wincert.__file__),Path(__file__)]}
results=[]
for shape in ['012301']:
 cache=H/'cache'/shape;cache.mkdir(parents=True);start=time.monotonic()
 enc=TaggedShare(list(map(int,shape)),[(0,21)]*5,14)
 for closing in [4,8]:enc.add([-enc.var[closing]],('old',('cut',)))
 cnf=cache/'input.cnf';raw=cache/'raw.lrat'
 with cnf.open('w',encoding='ascii',newline='\n') as f:
  f.write(f'p cnf {enc.nv} {len(enc.clauses)}\n')
  for cl in enc.clauses:f.write(' '.join(map(str,cl))+' 0\n')
 with gzip.open(H/'certificates'/(shape+'.cnf.gz'),'wb') as dest,cnf.open('rb') as src:
  import shutil;shutil.copyfileobj(src,dest)
 with gzip.open(H/'certificates'/(shape+'.meanings.json.gz'),'wt',encoding='utf-8') as f:
  json.dump(dict(meaning=enc.meaning,smeaning=enc.smeaning,ctrs=enc.ctrs,tots=enc.tots,tags=enc.tags),f)
 row={'shape':shape,'target_share':15,'cap':14,'count_bounds':[[0,21]]*5,'radius':4,'cycle_cuts':[[0,1,3,7,15,14,12,4],[0,1,3,7,15,14,12,8]],'closing_units':[4,8],'window':enc.window,'variables':enc.nv,'clauses':len(enc.clauses),'cnf_sha256':sha(cnf),'source_pins':pins,'status':'RUNNING','encoding_seconds':time.monotonic()-start,'peak_owned_private':mem(os.getpid())}
 del enc;gc.collect()
 stdout=H/'logs'/(shape+'.stdout');stderr=H/'logs'/(shape+'.stderr')
 command=[str(EXE),'-q','--lrat','--no-binary','--seed=1',str(cnf),str(raw)]
 row['command']=command;start=time.monotonic()
 with stdout.open('wb') as so,stderr.open('wb') as se:
  child=subprocess.Popen(command,stdout=so,stderr=se,creationflags=getattr(subprocess,'CREATE_NO_WINDOW',0))
  row['pid']=child.pid;save(H/'data'/(shape+'.json'),row)
  try:
   while child.poll() is None:
    s=nr.snapshot();private=mem(os.getpid())+mem(child.pid);row['peak_owned_private']=max(row['peak_owned_private'],private)
    if s['errors'] or s['processes'] or s['free_bytes']<768*1024**2 or private>512*1024**2:
     row['status']='RESOURCE_STOP';child.terminate();break
    if time.monotonic()-start>90 or (raw.exists() and raw.stat().st_size>128*1024**2):
     row['status']='BOUNDED_STOP';child.terminate();break
    time.sleep(.25)
   code=child.wait(timeout=15)
  finally:
   if child.poll() is None:child.terminate();child.wait(timeout=15)
 row.update(exit_code=code,solver_seconds=time.monotonic()-start,raw_bytes=raw.stat().st_size if raw.exists() else 0,raw_sha256=sha(raw) if raw.exists() else None)
 if row['status']=='RUNNING':row['status']='UNSAT_NATIVE_REPLAY_PENDING' if code==20 and b's UNSATISFIABLE' in stdout.read_bytes() else 'SAT_NATIVE' if code==10 else 'UNRESOLVED'
 if row['status']=='UNSAT_NATIVE_REPLAY_PENDING':
  with gzip.open(H/'certificates'/(shape+'.lrat.gz'),'wb') as dst,raw.open('rb') as src:shutil.copyfileobj(src,dst)
 row['artifacts']={p.name:sha(p) for p in (H/'certificates').glob(shape+'.*')}
 save(H/'data'/(shape+'.json'),row);results.append(row)
 print(shape,row['status'],round(row['solver_seconds'],2),row['raw_bytes'],flush=True)
for path,digest in pins.items():assert sha(path)==digest
save(H/'data/results.json',{'status':'FINISHED_BOUNDED_LOCAL_SEARCH','initial_resources':initial,'results':results,'Lean_replay':False,'actual_snake_bridge':False,'new_global_bound':False})
