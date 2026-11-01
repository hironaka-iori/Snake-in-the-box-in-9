"""Measure conditional-234 obligations after the share-120 premise; reuse fixed potential."""
from pathlib import Path
import collections,gzip,hashlib,json,sys
HERE=Path(__file__).resolve().parents[1];P=HERE.parent;ROOT=HERE.parents[2]
sys.path.insert(0,str(ROOT/'work/solver_packages'));import numpy as np
read=lambda p:json.loads(p.read_text());sha=lambda b:hashlib.sha256(b).hexdigest()
meta=read(P/'data/proved-model.json');sel=json.loads(gzip.decompress((P/'data/proved-old-selection.json.gz').read_bytes()))
with np.load(P/'build/proved-graph.npz') as z:a={k:z[k] for k in z.files}
for k,h in meta['arrays_sha256'].items():assert sha(a[k].tobytes())==h
sm=read(ROOT/'milestones/59-extended-share-window/extended/data/model.json');weight=a['weight'].astype(np.int64).copy();hit=np.zeros(len(weight),dtype=bool)
for di,ds in enumerate(sm['extensions']):
 if len(set(ds[-6:]))!=6:continue
 ix=np.flatnonzero(a['direction']==di);codes=a['count_code'][ix];cs=np.stack([codes//6**j%6+1 for j in range(4,-1,-1)],axis=1)
 hit[ix]=np.all(cs==[4,5,4,2,6],axis=1)|np.all(cs==[6,2,4,5,4],axis=1)
weight[hit]=np.maximum(weight[hit],120*(a['count_code'][hit]%6+1)+120)
raw=gzip.decompress((ROOT/'milestones/68-proof-dependency-pressure/data/share-clean-potential.i64.gz').read_bytes());assert sha(raw)==sel['potential_sha256'];pi=np.frombuffer(raw,dtype='<i8')
slack=29*weight+pi[a['U']]-pi[a['V']]-14387
basis=json.loads(gzip.decompress((ROOT/'milestones/68-proof-dependency-pressure/data/count-subsumption.json.gz').read_bytes()))['needed']
def canon(w):
 d={};return tuple(d.setdefault(x,len(d)) for x in w)
def encode(cs):
 x=0
 for c in cs:x=6*x+c-1
 return x
lookup={}
for i,(ds,cs) in enumerate(basis):
 for w,c in [(ds,cs),(ds[::-1],cs[::-1])]:
  word=canon(w);lookup.setdefault(word,np.full(6**len(c),-1,dtype=np.int32))[encode(c)]=i
clauses=set();negative=np.flatnonzero(slack<0)
for di,ds in enumerate(sm['extensions']):
 ix=negative[a['direction'][negative]==di];codes=a['count_code'][ix];matches=[]
 for start in range(5):
  for end in range(start+2,7):
   word=canon(ds[start+2:end+3])
   if word in lookup:matches.append(lookup[word][codes//6**(6-end)%6**(end-start)])
 matrix=np.stack(matches,axis=1) if matches else np.empty((len(ix),0),dtype=np.int32)
 for row in matrix:
  c=tuple(sorted(set(int(k) for k in row if k>=0)));assert c;clauses.add(c)
mandatory={c[0] for c in clauses if len(c)==1};assert all(mandatory.intersection(c) for c in clauses)
old=set(sel['selected_ids']);assert mandatory<=old
out=dict(status='EXACT_FIXED_POTENTIAL_CONDITIONAL_COMPARISON',share_premise=120,old_keys=len(old),new_keys=len(mandatory),removed_keys=sorted(old-mandatory),violating_edges=len(negative),all_violating_edges_covered=True,minimum_cover_certified_by_singleton_clauses=True,source_arrays_sha256=meta['arrays_sha256'],scope='Finite comparison with share-120 admitted. Other count premises and complete graph-to-snake proof remain unresolved.')
(HERE/'data/conditional-effect.json').write_text(json.dumps(out,indent=2)+'\n');print(out,flush=True)
