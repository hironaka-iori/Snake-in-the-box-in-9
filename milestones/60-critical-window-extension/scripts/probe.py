"""Compute every ten-transition extension of the saved twenty-step cycle."""
from pathlib import Path
from fractions import Fraction
import itertools,json
HERE=Path(__file__).resolve().parents[1];ROOT=HERE.parents[1]
cycle=json.loads((ROOT/'milestones/59-extended-share-window/extended/data/analysis-share.json').read_text())['cycle']
def canon(ds):
    seen={};return tuple(seen.setdefault(d,len(seen)) for d in ds)
def path(ds):
    W=[0]
    for d in ds:W.append(W[-1]^(1<<d))
    return W
def valid(W):
    return len(set(W))==len(W) and all((W[i]^W[j]).bit_count()!=1 for i in range(len(W)) for j in range(i+2,len(W)))
NB=[{x^(1<<d) for d in range(9)} for x in range(512)]
pairs=list(itertools.combinations(range(9),2))
records=[];phases=[]
for i,e in enumerate(cycle):
    nxt=cycle[(i+1)%len(cycle)];options=[]
    for d in range(min(9,max(e['directions'])+2)):
        ds=e['directions']+[d]
        if canon(ds[1:])!=tuple(nxt['directions']):continue
        W=path(ds)
        if not valid(W):continue
        D=set().union(*(NB[x] for x in W[1:-1]))-set(W);C=W[-6:-1]
        terms=[]
        for x in C:
            for q in sorted(NB[x]):
                empty=sum({q,q^(1<<a),q^(1<<b),q^(1<<a)^(1<<b)}<=D for a,b in pairs)
                denominator=len(NB[q]-D);assert denominator>0
                credit=12*empty//denominator
                if credit:terms.append(dict(centre=x,corner=q,empty=empty,degree_upper=denominator,credit=credit))
        lower=sum(t['credit'] for t in terms)
        weight=120*nxt['counts'][-1]+max(lower,nxt['share_lower'])
        r=dict(phase=i,directions=ds,vertices=W,centres=C,forced_absent=sorted(D),terms=terms,
               geometric_lower=lower,inherited_lower=nxt['share_lower'],counts=nxt['counts'],weight=weight)
        options.append(len(records));records.append(r)
    phases.append(dict(phase=i,options=options,minimum_weight=min((records[k]['weight'] for k in options),default=None)))
assert all(p['options'] for p in phases)
chosen=[min(p['options'],key=lambda k:records[k]['weight']) for p in phases]
mean=Fraction(sum(records[k]['weight'] for k in chosen),len(cycle))
# Ten-transition windows omit nine starts and retain 16 count units outside.
threshold=Fraction((1099800-240)-235*4200,235-9)
out=dict(status='COMPLETE_EXTENSIONS_OF_RECORDED_CYCLE',records=records,phases=phases,chosen=chosen,
         integer_weight_mean=str(mean),normalized_mean=str(mean/120),required_mean_zero_range=str(threshold),
         cycle_still_prevents_234=mean<=threshold,
         scope='Only extensions of the previously saved twenty-step cycle. No complete ten-transition model or global snake bound.')
(HERE/'data/probe.json').write_text(json.dumps(out,indent=2)+'\n')
print({k:v for k,v in out.items() if k not in ['records','phases','chosen']})
print('Extensions',len(records),'geometric shares',[(i,r['geometric_lower']) for i,r in enumerate(records)])
