"""Independent key matching, full retained-edge check and mandatory witnesses.

The source graph is the separately reconstructed round-70 enriched graph; this
check pins its arrays, and does not claim to prove their snake interpretation.
"""
from pathlib import Path
from fractions import Fraction
import collections,gzip,hashlib,json,sys,time
HERE=Path(__file__).resolve().parents[1];ROOT=HERE.parents[1]
sys.path.insert(0,str(ROOT/'work/solver_packages'))
import numpy as np
read=lambda p:json.loads(p.read_text(encoding='utf-8-sig'));sha=lambda b:hashlib.sha256(b).hexdigest()
started=time.monotonic();old=True;tag='proved-old-'
sel=json.loads(gzip.decompress((HERE/f'data/{tag}selection.json.gz').read_bytes()))
prior=HERE;meta=read(prior/'data/proved-model.json')
receipt=read(prior/'data/proved-graph-verification.json');assert receipt['status']=='PASS' and receipt['edges']==meta['edges']
with np.load(prior/'build/proved-graph.npz') as z:a={k:z[k] for k in z.files}
for k,h in meta['arrays_sha256'].items():assert sha(a[k].tobytes())==h
P=ROOT/'milestones/68-proof-dependency-pressure' if old else HERE
raw=gzip.decompress((P/('data/share-clean-potential.i64.gz' if old else 'data/potential.i64.gz')).read_bytes())
assert sha(raw)==sel['potential_sha256'];pi=np.frombuffer(raw,dtype='<i8')
p,d,R=sel['potential_numerator'],sel['potential_denominator'],sel['potential_range']
assert int(max(pi)-min(pi))==R and len(pi)==meta['states']
basis=json.loads(gzip.decompress((ROOT/'milestones/68-proof-dependency-pressure/data/count-subsumption.json.gz').read_bytes()))['needed']
selected=set(sel['selected_ids']);assert sel['keys']==[basis[k] for k in sorted(selected)]
sm=read(ROOT/'milestones/59-extended-share-window/extended/data/model.json')
def canon(w):
    seen={};return tuple(seen.setdefault(x,len(seen)) for x in w)
def encode(c):
    n=0
    for x in c:n=n*6+x-1
    return n
lookup=collections.defaultdict(dict)
for k,(w,c) in enumerate(basis):
    for ww,cc in [(w,c),(w[::-1],c[::-1])]:lookup[canon(ww)][tuple(cc)]=k
def hits(ds,cs):
    result=set()
    for start in range(5):
        for end in range(start+2,7):
            word=canon(ds[start+2:end+3]);key=lookup.get(word,{}).get(tuple(cs[start:end]))
            if key is not None:result.add(key)
    return result
singletons=[c for c in sel['clauses'] if len(c['keys'])==1]
assert selected=={c['keys'][0] for c in singletons}
assert all(selected.intersection(c['keys']) for c in sel['clauses'])
slack=d*a['weight'].astype(np.int64)+pi[a['U']]-pi[a['V']]-p
for row in singletons:
    e=row['example'];i=e['edge'];di=e['direction'];code=e['count_code']
    assert (int(a['direction'][i]),int(a['history'][i]),int(a['count_code'][i]))==(di,e['history'],code)
    cs=[code//6**j%6+1 for j in range(5,-1,-1)]
    assert hits(sm['extensions'][di],cs)==set(row['keys'])
    assert int(slack[i])==e['slack']<0
keep=np.ones(len(slack),dtype=bool);allkeep=keep.copy()
for di,ds in enumerate(sm['extensions']):
    ix=np.flatnonzero(a['direction']==di);codes=a['count_code'][ix]
    removed=np.zeros(len(ix),dtype=bool);anyremoved=removed.copy()
    for start in range(5):
        for end in range(start+2,7):
            word=canon(ds[start+2:end+3]);table=lookup.get(word,{})
            if not table:continue
            subcodes=codes//6**(6-end)%6**(end-start)
            removed|=np.isin(subcodes,[encode(c) for c,k in table.items() if k in selected])
            anyremoved|=np.isin(subcodes,[encode(c) for c in table])
    keep[ix]=~removed;allkeep[ix]=~anyremoved
assert np.all(slack[keep]>=0)
assert int((slack<0).sum())==sel['violating_edges']
assert len(slack)==sel['candidate_edges']
coef=p+4200*d;const=1098960*d+8*p+R
assert (coef,const,235*coef-const)==(sel['bound_coefficient'],sel['bound_constant'],sel['margin_at_235'])
assert const//coef==234 and (p-1+4200*d)*235<=1098960*d+8*(p-1)+R
out={k:v[keep] for k,v in a.items()};np.savez_compressed(HERE/f'build/{tag}selected-graph.npz',**out)
report=dict(status='PASS',candidate_edges=len(slack),retained_edges=int(keep.sum()),mandatory_witnesses=len(singletons),selected_keys=len(selected),unique_least_cover_for_fixed_potential=True,potential_mean=str(Fraction(p,d)),potential_range=R,bound_coefficient=coef,bound_constant=const,conditional_integer_bound=const//coef,source_arrays_sha256=meta['arrays_sha256'],selected_arrays_sha256={k:sha(v.tobytes()) for k,v in out.items()},seconds=time.monotonic()-started,scope='Independent basis matching, all retained-edge inequalities and mandatory witnesses on the independently verified round-72 proved graph. Conditional count premises and global Lean assembly remain unresolved.')
(HERE/f'data/{tag}verification.json').write_text(json.dumps(report,indent=2)+'\n');print(report,flush=True)
