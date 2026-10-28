"""Lift the previous model to nine transitions and retain its last five centres."""
from pathlib import Path
import hashlib, importlib.util, itertools, json, sys
HERE=Path(__file__).resolve().parents[1]; ROOT=HERE.parents[1]
sys.path.insert(0,str(ROOT/'milestones/42-six-count-state-model/scripts'))
import model
np=model.np
SOURCE=ROOT/'milestones/58-share-pressure/geometry'
meta=json.loads((SOURCE/'data/model.json').read_text())
with np.load(SOURCE/'build/graph.npz') as z: old={k:z[k] for k in z.files}
for k,h in meta['arrays_sha256'].items():
    assert hashlib.sha256(old[k].tobytes()).hexdigest()==h
shapes=[tuple(s) for s in meta['extensions']]; sid={s:i for i,s in enumerate(shapes)}
words=list(model.words(9)); records=[]; arrays={k:[] for k in old}; parent=[]
nb=[{x^(1<<d) for d in range(9)} for x in range(512)]
pairs=list(itertools.combinations(range(9),2))
oldgeom=json.loads((ROOT/'milestones/58-share-pressure/data/forced-geometry.json').read_text())['patterns']
for di,ds in enumerate(words):
    W=[0]
    for d in ds: W.append(W[-1]^(1<<d))
    D=set().union(*(nb[x] for x in W[1:-1]))-set(W)
    C=W[-6:-1]; terms=[]
    for x in C:
        for q in sorted(nb[x]):
            empty=sum({q,q^(1<<a),q^(1<<b),q^(1<<a)^(1<<b)}<=D for a,b in pairs)
            upper=len(nb[q]-D); assert upper>0
            value=12*empty//upper
            if value: terms.append(dict(centre=x,corner=q,empty=empty,degree_upper=upper,credit=value))
    lower=sum(t['credit'] for t in terms)
    pi=sid[model.canon(ds[:8])]; si=sid[model.canon(ds[1:])]
    assert lower>=oldgeom[si]['share_lower']
    records.append(dict(directions=ds,vertices=W,centres=C,forced_absent=sorted(D),
                        share_lower=lower,suffix_lower=oldgeom[si]['share_lower'],terms=terms))
    ix=np.flatnonzero(old['direction']==si); codes=old['count_code'][ix]
    arrays['U'].append(pi*6**5+codes//6)
    arrays['V'].append(si*6**5+codes%(6**5))
    arrays['direction'].append(np.full(len(ix),di,dtype=np.int16))
    for k in ['count','count_code','share_lower']: arrays[k].append(old[k][ix])
    parent.append(ix)
arrays={k:np.concatenate(v) for k,v in arrays.items()}
parent=np.concatenate(parent)
(HERE/'data/geometry.json').write_text(json.dumps(dict(patterns=records,
    scope='Computed nine-transition forced-absence certificates; Lean proof status recorded separately.'),indent=2)+'\n')
geocredit=np.array([r['share_lower'] for r in records],dtype=np.int16)[arrays['direction']]
for name in ['lifted','extended']:
    a=dict(arrays)
    if name=='extended': a['share_lower']=np.maximum(a['share_lower'],geocredit)
    dest=HERE/name;(dest/'build').mkdir(parents=True,exist_ok=True);(dest/'data').mkdir(exist_ok=True)
    np.savez_compressed(dest/'build/graph.npz',**a)
    out=dict(states=len(shapes)*6**5,edges=len(a['U']),direction_shapes=shapes,extensions=words,
             source=SOURCE.relative_to(ROOT).as_posix(),boundary_lost_windows=8,
             strengthened_transitions=int((a['share_lower']>arrays['share_lower']).sum()),
             arrays_sha256={k:hashlib.sha256(v.tobytes()).hexdigest() for k,v in a.items()},
             scope='Lift of the prior conditional model. Inherited numerical premises and full graph-to-snake assembly remain pending.')
    (dest/'data/model.json').write_text(json.dumps(out,indent=2)+'\n')
    print(name,'states',out['states'],'edges',out['edges'],'strengthened',out['strengthened_transitions'],flush=True)
print('Shapes',len(records),'positive',sum(r['share_lower']>0 for r in records),'improved',sum(r['share_lower']>r['suffix_lower'] for r in records),'max',max(r['share_lower'] for r in records),flush=True)
