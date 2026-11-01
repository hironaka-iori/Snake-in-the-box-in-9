"""Exact fixed-potential comparison; unproved shape bounds stay explicit premises."""
from pathlib import Path
import gzip,hashlib,json,sys
HERE=Path(__file__).resolve().parents[1];ROOT=HERE.parents[2];P=HERE.parent
sys.path.insert(0,str(ROOT/'work/solver_packages'));import numpy as np
read=lambda p:json.loads(p.read_text());sha=lambda b:hashlib.sha256(b).hexdigest()
args=sys.argv[1:];share=next((int(s.split('=')[1]) for s in args if s.startswith('--share=')),12)
assert share>=0
overrides={s.split('=')[1].split(':')[0]:int(s.split(':')[1]) for s in args if s.startswith('--override=')}
assert all(v>=0 for v in overrides.values())
args=[s for s in args if not s.startswith(('--share=','--override='))]
shapes=([tuple(s) for s in read(HERE/'data/all-six-direction-shapes.json')['up_to_reversal']] if '--all' in args else [tuple(map(int,s)) for s in args]) or [(0,1,2,3,4,5)]
tag=('countfree-' if share==12 else f'countfree{share}-')+('all' if '--all' in args else '-'.join(''.join(map(str,s)) for s in shapes))
tag+=''.join(f'-except{k}x{v}' for k,v in sorted(overrides.items()))
def canon(w):
 d={};return tuple(d.setdefault(x,len(d)) for x in w)
shapes={min(canon(s),canon(s[::-1])) for s in shapes}
meta=read(HERE/'data/source-proved-model.json')
with np.load(HERE/'build/source-graph.npz') as z:a={k:z[k] for k in z.files}
for k,h in meta['arrays_sha256'].items():assert sha(a[k].tobytes())==h
sm=read(ROOT/'milestones/59-extended-share-window/extended/data/model.json')
weight=a['weight'].astype(np.int64).copy();hit=np.zeros(len(weight),dtype=bool);extra=np.zeros(len(weight),dtype=np.int64)
for di,ds in enumerate(sm['extensions']):
 shape=min(canon(ds[-6:]),canon(ds[-6:][::-1]))
 if shape in shapes:
  ix=a['direction']==di;hit|=ix;extra[ix]=overrides.get(''.join(map(str,shape)),share)
weight[hit]=np.maximum(weight[hit],120*(a['count_code'][hit]%6+1)+extra[hit])
raised=weight>a['weight'];a['weight']=weight
sel=read(P/'critical-charge/data/conditional-effect.json');old=set(range(25279))
raw=gzip.decompress((ROOT/'milestones/68-proof-dependency-pressure/data/share-clean-potential.i64.gz').read_bytes())
assert sha(raw)=='ef08dbc13f63711bf7595e310f47601aa1f652a974f156689de0eeeea29e1793'
pi=np.frombuffer(raw,dtype='<i8');slack=29*weight+pi[a['U']]-pi[a['V']]-14387
basis=json.loads(gzip.decompress((ROOT/'milestones/68-proof-dependency-pressure/data/count-subsumption.json.gz').read_bytes()))['needed']
def encode(cs):
 x=0
 for c in cs:x=6*x+c-1
 return x
lookup={}
for i,(ds,cs) in enumerate(basis):
 for w,c in [(ds,cs),(ds[::-1],cs[::-1])]:
  lookup.setdefault(canon(w),np.full(6**len(c),-1,dtype=np.int32))[encode(c)]=i
clauses=set();negative=np.flatnonzero(slack<0)
for di,ds in enumerate(sm['extensions']):
 ix=negative[a['direction'][negative]==di];codes=a['count_code'][ix];matches=[]
 for start in range(5):
  for end in range(start+2,7):
   word=canon(ds[start+2:end+3])
   if word in lookup:matches.append(lookup[word][codes//6**(6-end)%6**(end-start)])
 matrix=np.stack(matches,axis=1) if matches else np.empty((len(ix),0),dtype=np.int32)
 for row in matrix:
  clause=tuple(sorted(set(int(k) for k in row if k>=0)));assert clause;clauses.add(clause)
mandatory={c[0] for c in clauses if len(c)==1};assert all(mandatory.intersection(c) for c in clauses)
old=set(json.loads(gzip.decompress((P/'data/proved-old-selection.json.gz').read_bytes()))['selected_ids'])-set(sel['removed_keys'])
assert mandatory<=old
critical=read(HERE/'data/critical-edges.json');ce=[e for e in critical if raised[e['source_edge']]]
meta.update(arrays_sha256={k:sha(v.tobytes()) for k,v in a.items()},countfree_shapes=[list(s) for s in sorted(shapes)],countfree_share_lower=share,countfree_overrides=overrides,scope='Conditional finite graph. Every listed count-free shape inequality must be Lean-checked before theorem use; global graph interpretation remains pending.')
np.savez_compressed(HERE/f'build/{tag}-graph.npz',**a)
(HERE/f'data/{tag}-model.json').write_text(json.dumps(meta,indent=2)+'\n')
out=dict(status='EXACT_CONDITIONAL_COMPARISON',shapes=[list(s) for s in sorted(shapes)],share_lower=share,overrides=overrides,improved_edges=int(raised.sum()),improved_critical_edges=len(ce),old_keys=len(old),new_keys=len(mandatory),removed_keys=sorted(old-mandatory),violating_edges=len(negative),all_violating_edges_covered=True,minimum_cover_certified_by_singleton_clauses=True,potential_sha256=sha(raw),source_arrays_sha256=read(HERE/'data/source-proved-model.json')['arrays_sha256'],scope=meta['scope'])
(HERE/f'data/{tag}-effect.json').write_text(json.dumps(out,indent=2)+'\n')
print({k:v for k,v in out.items() if k not in ['removed_keys','source_arrays_sha256']},flush=True)
