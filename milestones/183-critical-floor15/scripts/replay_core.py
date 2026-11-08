"""Stream the full LRAT proofs, honoring deletions and checking every RUP step.

This is native proof replay, not a Lean kernel certificate or semantic bridge.
"""
from pathlib import Path
import sys,json,gzip,hashlib,time,os
import native_resources as nr
H=Path(__file__).resolve().parents[1];R=H.parents[1]
def sha(p):
 h=hashlib.sha256()
 with Path(p).open('rb') as f:
  for b in iter(lambda:f.read(1048576),b''):h.update(b)
 return h.hexdigest()
def private():
 handle=nr.kernel.OpenProcess(0x1000,False,os.getpid());v=nr.PROCESS_MEMORY_COUNTERS_EX();v.cb=nr.ctypes.sizeof(v)
 try:
  assert nr.psapi.GetProcessMemoryInfo(handle,nr.ctypes.byref(v),v.cb)
  return int(v.PrivateUsage)
 finally:nr.kernel.CloseHandle(handle)
base=H;outputs=[]
for shape in ['012034-floor15-core']:
 start=time.monotonic();record={'shape':shape,'status':'RUNNING','checker_sha256':sha(__file__)}
 db={};lemmas=hints=deletions=0;final_empty=False;peak=private()
 try:
  s=nr.snapshot();assert not s['processes'] and not s['errors'] and s['free_bytes']>=1024**3,s
  native=json.loads((base/'data/012034-floor15-core.json').read_text());assert native['status']=='UNSAT_NATIVE_REPLAY_PENDING'
  cnf=base/'certificates'/(shape+'.cnf.gz');proof=base/'certificates'/(shape+'.lrat.gz')
  assert sha(cnf)==native['artifacts'][cnf.name] and sha(proof)==native['artifacts'][proof.name]
  chash=hashlib.sha256()
  with gzip.open(cnf,'rb') as f:
   header=f.readline();chash.update(header);_,_,nv,nc=header.split();nv=int(nv);nc=int(nc)
   for i,line in enumerate(f,1):
    chash.update(line);vals=list(map(int,line.split()));assert vals[-1]==0
    assert all(0<abs(x)<=nv for x in vals[:-1]);db[i]=vals[:-1]
  assert i==nc and chash.hexdigest()==native['cnf_sha256'];previous=nc
  phash=hashlib.sha256()
  with gzip.open(proof,'rb') as f:
   for lineno,line in enumerate(f,1):
    phash.update(line);tokens=line.split()
    if tokens[1]==b'd':
     assert tokens[-1]==b'0'
     for key in map(int,tokens[2:-1]):db.pop(key,None);deletions+=1
     continue
    values=list(map(int,tokens));zero=values.index(0,1);cid=values[0];cl=values[1:zero];hs=values[zero+1:-1]
    assert values[-1]==0 and cid>previous and cid not in db
    assert all(0<abs(x)<=nv for x in cl) and all(0<h<cid for h in hs)
    previous=cid;assignment={};conflict=False
    for lit in cl:
     var,value=abs(lit),lit<0
     if var in assignment and assignment[var]!=value:conflict=True
     assignment[var]=value
    for hint in hs:
     assert hint in db,(cid,hint,'missing hint')
     if conflict:continue
     unseen=set();satisfied=False
     for lit in db[hint]:
      value=assignment.get(abs(lit))
      if value is None:unseen.add(lit)
      elif value==(lit>0):satisfied=True
     assert not satisfied and len(unseen)<=1,(cid,hint,'nonunit or satisfied')
     if not unseen:conflict=True
     else:
      unit=next(iter(unseen));assignment[abs(unit)]=unit>0
    assert conflict,(cid,'RUP failed')
    db[cid]=cl;lemmas+=1;hints+=len(hs)
    if not cl:final_empty=True
    if lemmas%2000==0:
     peak=max(peak,private());s=nr.snapshot()
     assert not s['errors'] and not s['processes'] and s['free_bytes']>=768*1024**2 and peak<=256*1024**2,'RESOURCE_STOP'
     assert time.monotonic()-start<240,'TIME_LIMIT'
  assert final_empty and phash.hexdigest()==native['raw_sha256']
  record.update(status='PASS_FULL_ORDERED_RUP_REPLAY',cnf_sha256=chash.hexdigest(),lrat_sha256=phash.hexdigest(),final_empty_clause=True)
 except Exception as error:record.update(status='UNRESOLVED_REPLAY',error=repr(error))
 record.update(lemmas=lemmas,hints=hints,deletions=deletions,peak_private=peak,seconds=time.monotonic()-start)
 (H/'data'/(shape+'-replay.json')).write_text(json.dumps(record,indent=2)+'\n');outputs.append(record)
 print(shape,record['status'],lemmas,hints,round(record['seconds'],2),record.get('error',''),flush=True)
 del db
(H/'data/core-replays.json').write_text(json.dumps(outputs,indent=2)+'\n')
