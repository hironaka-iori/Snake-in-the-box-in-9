"""Retain the full dependency closure of an already replayed RUP refutation."""
from pathlib import Path
import gzip,hashlib,json,os,time
import native_resources as nr
H=Path(__file__).resolve().parents[1]

def sha(p):
 h=hashlib.sha256()
 with Path(p).open('rb') as f:
  for b in iter(lambda:f.read(1048576),b''):h.update(b)
 return h.hexdigest()

def private():
 h=nr.kernel.OpenProcess(0x1000,False,os.getpid())
 try:
  v=nr.PROCESS_MEMORY_COUNTERS_EX();v.cb=nr.ctypes.sizeof(v)
  assert nr.psapi.GetProcessMemoryInfo(h,nr.ctypes.byref(v),v.cb)
  return int(v.PrivateUsage)
 finally:nr.kernel.CloseHandle(h)

start=time.monotonic();initial=nr.snapshot()
assert not initial['processes'] and not initial['errors'] and initial['free_bytes']>=1024**3,initial
meta=json.loads((H/'data/012034-floor15.json').read_text())
accepted=json.loads((H/'data/012034-floor15-replay.json').read_text())
assert accepted['status']=='PASS_FULL_ORDERED_RUP_REPLAY'
raw=H/'cache/012034-floor15/raw.lrat';cnf=H/'cache/012034-floor15/input.cnf'
assert sha(raw)==meta['raw_sha256'] and sha(cnf)==meta['cnf_sha256']
index={};empty=None;count=0;peak=private()
def guard():
 global peak
 s=nr.snapshot();peak=max(peak,private())
 assert not s['processes'] and not s['errors'] and s['free_bytes']>=768*1024**2 and peak<=256*1024**2,s
 assert time.monotonic()-start<240

with raw.open('rb') as f:
 while True:
  offset=f.tell();line=f.readline()
  if not line:break
  tokens=line.split()
  if tokens[1]==b'd':continue
  cid=int(tokens[0]);index[cid]=offset;count+=1
  if tokens[1]==b'0':empty=cid
  if count%5000==0:guard()
assert empty is not None
needed={empty};todo=[empty];inputs=set();visits=0
with raw.open('rb') as f:
 while todo:
  cid=todo.pop();f.seek(index[cid]);vals=list(map(int,f.readline().split()));z=vals.index(0,1)
  assert vals[0]==cid and vals[-1]==0
  for hint in vals[z+1:-1]:
   assert 0<hint<cid
   if hint<=meta['clauses']:inputs.add(hint)
   elif hint not in needed:needed.add(hint);todo.append(hint)
  visits+=1
  if visits%5000==0:guard()
mapping={old:new for new,old in enumerate(sorted(inputs)+sorted(needed),1)}
label='012034-floor15-core';outcnf=H/'cache'/(label+'.cnf');outproof=H/'cache'/(label+'.lrat')
core_original=[]
with cnf.open('rb') as src,outcnf.open('wb') as dst:
 header=src.readline();dst.write(f'p cnf {meta["variables"]} {len(inputs)}\n'.encode())
 for cid,line in enumerate(src,1):
  if cid in inputs:dst.write(line);core_original.append(cid)
assert len(core_original)==len(inputs)
hint_count=0
with raw.open('rb') as src,outproof.open('w',encoding='ascii',newline='\n') as dst:
 for cid in sorted(needed):
  src.seek(index[cid]);values=list(map(int,src.readline().split()));z=values.index(0,1)
  hints=[mapping[x] for x in values[z+1:-1]];hint_count+=len(hints)
  dst.write(' '.join(map(str,[mapping[cid],*values[1:z],0,*hints,0]))+'\n')
  if mapping[cid]%5000==0:guard()
import shutil
for suffix,path in [('cnf',outcnf),('lrat',outproof)]:
 with path.open('rb') as src,gzip.open(H/'certificates'/(label+'.'+suffix+'.gz'),'wb') as dst:shutil.copyfileobj(src,dst)
with gzip.open(H/'certificates'/(label+'.mapping.json.gz'),'wt') as f:
 json.dump({'original_input_ids':core_original,'original_derived_ids':sorted(needed)},f)
result={'status':'UNSAT_NATIVE_REPLAY_PENDING','source_replay_sha256':sha(H/'data/012034-floor15-replay.json'),
 'source_cnf_sha256':meta['cnf_sha256'],'source_lrat_sha256':meta['raw_sha256'],
 'producer_sha256':sha(__file__),'variables':meta['variables'],'clauses':len(inputs),
 'derived_clauses':len(needed),'hints':hint_count,'cnf_sha256':sha(outcnf),'raw_sha256':sha(outproof),
 'raw_bytes':outproof.stat().st_size,'original_derived':count,'original_hints':accepted['hints'],
 'seconds':time.monotonic()-start,'peak_private':peak,'initial_resources':initial}
result['artifacts']={p.name:sha(p) for p in (H/'certificates').glob(label+'.*')}
(H/'data'/(label+'.json')).write_text(json.dumps(result,indent=2)+'\n')
print('TRIMMED',len(inputs),'inputs',len(needed),'derived',hint_count,'hints',result['raw_bytes'],'bytes',flush=True)
