"""Six-count memory model using only identified proved local premises.

The finite graph remains a computational model until its complete arbitrary-snake
bridge is checked. Symbol6 denotes [6,21], never an exact singleton count.
"""
from pathlib import Path
import ast,hashlib,itertools,json,re,sys,time
ROOT=Path(__file__).resolve().parents[3];HERE=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'work/solver_packages'))
import numpy as np

def canon(ds):
 names={};return tuple(names.setdefault(d,len(names)) for d in ds)
def induced(ds):
 p=[0]
 for d in ds:p.append(p[-1]^(1<<d))
 return len(p)==len(set(p)) and all((p[i]^p[j]).bit_count()!=1 for i in range(len(p)) for j in range(i+2,len(p)))
def words(n,p=()):
 if not n:yield p;return
 for d in range(min(9,max(p,default=-1)+2)):
  q=p+(d,)
  if induced(q):yield from words(n-1,q)
def code(a):
 out=np.zeros(len(a),dtype=np.int32)
 for j in range(a.shape[1]):out=6*out+a[:,j]-1
 return out
def forbidden_tables():
 path=ROOT/'milestones/39-audited-bound-236/data/exclusion-catalogue.json'
 keys=json.loads(path.read_text());assert len(keys)==732
 tables={}
 for ds,cs in keys:
  for d,a in [(canon(ds),cs),(canon(ds[::-1]),cs[::-1])]:
   tables.setdefault(d,np.zeros(6**len(a),dtype=bool))[int(code(np.array([a]))[0])]=True
 return tables
def four_run_words():
 out=set()
 for i in [0,1,14,22]:
  s=(ROOT/f'milestones/32-seven-count-four-screen/lean/RunWindow{i}.lean').read_text(encoding='utf-8')
  ds=ast.literal_eval(re.search(r'def directions : List Nat := (\[[^\n]+\])',s)[1])
  out.update([canon(ds),canon(ds[::-1])])
 return out

def extras(ds,A):
 """Return forbidden mask, maximum seven-position excess demand, and forward share event."""
 bad=np.zeros(len(A),dtype=bool);D=np.zeros(len(A),dtype=np.int16)
 runs=four_run_words()
 for reverse in [False,True]:
  word=ds[::-1] if reverse else ds;B=A[:,::-1] if reverse else A
  for offset in [0,1]:
   w=canon(word[offset:offset+7]);b=B[:,offset:offset+6]
   if w in runs:bad|=np.all(b==4,axis=1)
   K=10 if w==(0,1,2,3,4,1,0) else 9 if w==(0,1,2,3,4,1,5) else 0
   if K:
    missing=np.maximum(0,K-b[:,0]-b[:,5]);bad|=(missing>0)&(b[:,0]<6)&(b[:,5]<6);D=np.maximum(D,missing)
  for offset in range(3):
   if canon(word[offset:offset+6])==(0,1,2,0,3,1):bad|=np.all(B[:,offset:offset+5]==[2,4,5,3,3],axis=1)
  w=canon(word)
  if w==(0,1,2,3,0,4,2,3):bad|=np.all(B==[3,5,4,4,5,3,3],axis=1)
  if w==(0,1,2,3,4,2,0,3):
   X,Y=B[:,0],B[:,6]
   bad|=(X==1)|((X<=2)&(Y<=3))|((Y==1)&(X<6))
   D=np.maximum(D,np.where(Y==1,np.maximum(0,9-X),0))
   low=(X<=3)&(Y<=3)
   bad|=low&((B[:,2]<5)|(B[:,5]<5))
   gap=np.maximum(0,12-B[:,2]-B[:,5])
   bad|=low&(gap>0)&(B[:,2]<6)&(B[:,5]<6)
   D=np.maximum(D,np.where(low,gap,0))
  if w in [(0,1,2,3,4,1,2,0),(0,1,2,3,4,1,2,5)]:
   hit=np.all(B==[6,3,3,6,3,3,6],axis=1)
   D=np.maximum(D,np.where(hit,11 if w[-1]==0 else 10,0))
 share=int(canon(ds[1:])==(0,1,2,3,4,1,5))
 return bad,D,share

def build():
 start=time.monotonic();(HERE/'build').mkdir(parents=True,exist_ok=True);(HERE/'data').mkdir(exist_ok=True)
 shapes=list(words(7));extensions=list(words(8));assert len(shapes)==34 and len(extensions)==132
 sid={s:i for i,s in enumerate(shapes)};tables=forbidden_tables()
 A=np.array(list(itertools.product(range(1,7),repeat=7)),dtype=np.int16)
 first,last=code(A[:,:6]),code(A[:,1:]);U=[];V=[];W=[];BAD=[];DEMAND=[];SHARE=[];DS=[];AI=[]
 for di,ds in enumerate(extensions):
  keep=np.ones(len(A),dtype=bool)
  for k in range(2,6):
   for offset in range(8-k):
    table=tables.get(canon(ds[offset:offset+k+1]))
    if table is not None:keep &= ~table[code(A[:,offset:offset+k])]
  ids=np.flatnonzero(keep);B=A[ids];bad,demand,share=extras(ds,B)
  U.append(sid[canon(ds[:7])]*6**6+first[ids]);V.append(sid[canon(ds[1:])]*6**6+last[ids]);W.append(B[:,-1]);BAD.append(bad);DEMAND.append(demand);SHARE.append(np.full(len(ids),share,np.int8));DS.append(np.full(len(ids),di,np.int16));AI.append(ids)
  if di%20==0:print('Built direction block',di,'of',len(extensions),flush=True)
 arrays=dict(U=np.concatenate(U),V=np.concatenate(V),count=np.concatenate(W),excluded=np.concatenate(BAD),demand=np.concatenate(DEMAND),share=np.concatenate(SHARE),direction=np.concatenate(DS),count_code=np.concatenate(AI))
 np.savez_compressed(HERE/'build/graph.npz',**arrays)
 out=dict(states=len(shapes)*6**6,base_edges=len(arrays['U']),excluded_edges=int(arrays['excluded'].sum()),remaining_edges=int((~arrays['excluded']).sum()),direction_shapes=shapes,extensions=extensions,seconds=round(time.monotonic()-start,3),arrays_sha256={k:hashlib.sha256(v.tobytes()).hexdigest() for k,v in arrays.items()},scope='Finite computational model; only documented proved local premises, no unproved six-count-four rule. Full graph-to-snake Lean bridge remains pending.')
 (HERE/'data/model.json').write_text(json.dumps(out,indent=2)+'\n');print({k:v for k,v in out.items() if k not in ['direction_shapes','extensions','arrays_sha256']},flush=True)
if __name__=='__main__':build()
