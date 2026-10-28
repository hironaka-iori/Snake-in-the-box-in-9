"""Extend the unique recorded cycle windows until branching or incompatibility."""
from pathlib import Path
from fractions import Fraction
import itertools,json
HERE=Path(__file__).resolve().parents[1]
initial=json.loads((HERE/'data/probe.json').read_text())
prev=initial['records'];assert len(prev)==20 and all(len(p['options'])==1 for p in initial['phases'])
def canon(ds):
    seen={};return tuple(seen.setdefault(d,len(seen)) for d in ds)
def path(ds):
    W=[0]
    for d in ds:W.append(W[-1]^(1<<d))
    return W
def valid(W):
    return len(set(W))==len(W) and all((W[i]^W[j]).bit_count()!=1 for i in range(len(W)) for j in range(i+2,len(W)))
NB=[{x^(1<<d) for d in range(9)} for x in range(512)]
pairs=list(itertools.combinations(range(9),2));levels=[]
for length in range(11,17):
    records=[];counts=[]
    for i,r in enumerate(prev):
        nxt=prev[(i+1)%20];options=[]
        for d in range(min(9,max(r['directions'])+2)):
            ds=r['directions']+[d]
            if canon(ds[1:])!=tuple(nxt['directions']):continue
            W=path(ds)
            if not valid(W):continue
            D=set().union(*(NB[x] for x in W[1:-1]))-set(W);C=W[-6:-1];terms=[]
            for x in C:
                for q in sorted(NB[x]):
                    e=sum({q,q^(1<<a),q^(1<<b),q^(1<<a)^(1<<b)}<=D for a,b in pairs)
                    degree=len(NB[q]-D);assert degree>0
                    credit=12*e//degree
                    if credit:terms.append(dict(centre=x,corner=q,empty=e,degree_upper=degree,credit=credit))
            lower=sum(t['credit'] for t in terms);inherited=max(nxt['geometric_lower'],nxt['inherited_lower'])
            options.append(dict(phase=i,directions=ds,vertices=W,centres=C,forced_absent=sorted(D),terms=terms,
                                geometric_lower=lower,inherited_lower=inherited,counts=nxt['counts'],
                                weight=120*nxt['counts'][-1]+max(lower,inherited)))
        counts.append(len(options));records.extend(options)
    out=dict(length=length,extension_counts=counts,records=records)
    if any(n!=1 for n in counts):
        out['status']='STOPPED_AT_BRANCH_OR_MISSING_EXTENSION';levels.append(out);break
    mean=Fraction(sum(r['weight'] for r in records),20)
    A=1099800-120*(length-8);threshold=Fraction(A-235*4200,235-(length-1))
    out.update(status='UNIQUE_CYCLE_EXTENSION',integer_weight_mean=str(mean),normalized_mean=str(mean/120),
               required_mean_zero_range=str(threshold),cycle_still_prevents_234=mean<=threshold)
    levels.append(out);prev=records
    print({k:v for k,v in out.items() if k not in ['records','extension_counts']},flush=True)
    if mean>threshold:break
(HERE/'data/deeper-probe.json').write_text(json.dumps(dict(levels=levels,scope='Successive unique extensions of one recorded cycle, not a complete global model.'),indent=2)+'\n')
print('Final',length,levels[-1]['status'],counts)
