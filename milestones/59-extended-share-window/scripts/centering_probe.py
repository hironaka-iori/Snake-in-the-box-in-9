"""Evaluate a proposed centred charge on the existing cycle only."""
from pathlib import Path
from fractions import Fraction
import itertools,json
HERE=Path(__file__).resolve().parents[1];ROOT=HERE.parents[1]
read=lambda p:json.loads(p.read_text())
def canon(ds):
    names={};return tuple(names.setdefault(x,len(names)) for x in ds)
geometry={tuple(r['directions']):r for r in read(HERE/'data/geometry.json')['patterns']}
cycle=read(HERE/'extended/data/analysis-share.json')['cycle']
rules=read(ROOT/'milestones/58-share-pressure/geometry/data/model.json')['share_rules']
pairs=list(itertools.combinations(range(9),2));rows=[]
for e in cycle:
    r=geometry[tuple(e['directions'])];D=set(r['forced_absent']);C=r['vertices'][3:8]
    lower=0
    for x in C:
        for d in range(9):
            q=x^(1<<d)
            n=sum({q,q^(1<<a),q^(1<<b),q^(1<<a)^(1<<b)}<=D for a,b in pairs)
            denominator=sum(q^(1<<k) not in D for k in range(9))
            assert denominator>0
            lower+=12*n//denominator
    shape=canon(e['directions'][2:8]);counts=e['counts'][:5]
    inherited=max([0]+[r['lower'] for r in rules if tuple(r['directions'])==shape and r['counts']==counts])
    rows.append(dict(directions=e['directions'],counts=e['counts'],centred_geometry=lower,
                     inherited_lower=inherited,weight=120*e['counts'][-1]+max(lower,inherited)))
mu=Fraction(sum(r['weight'] for r in rows),len(rows))
threshold=Fraction(1099680-235*4200,235-8)
out=dict(status='CYCLE_ONLY_PROBE',cycle_length=len(rows),centred_cycle_mean=str(mu),
         normalized_mean=str(mu/120),required_mean_at_zero_range=str(threshold),
         this_cycle_still_prevents_234=mu<=threshold,rows=rows,
         scope='Only the saved twenty-edge cycle was evaluated. No complete centred model, potential or new centred Lean catalogue is claimed.')
(HERE/'data/centering-probe.json').write_text(json.dumps(out,indent=2)+'\n')
print({k:v for k,v in out.items() if k!='rows'})
