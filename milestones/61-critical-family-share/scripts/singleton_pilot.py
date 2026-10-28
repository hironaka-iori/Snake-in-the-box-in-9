"""Exploratory one-singleton branch calculation; no proof replay is claimed."""
from pathlib import Path
import itertools,json
HERE=Path(__file__).resolve().parents[1]
edges=json.loads((HERE/'data/critical-edges.json').read_text())
NB=[{x^(1<<d) for d in range(9)} for x in range(512)]
pairs=list(itertools.combinations(range(9),2));results=[]
for index,e in enumerate(edges):
    W=[0]
    for d in e['directions']:W.append(W[-1]^(1<<d))
    trials=[]
    for k,count in enumerate(e['counts']):
        if count!=1:continue
        j=k+3;x=W[j]
        free=[d for d in range(9) if d not in [e['directions'][j-1],e['directions'][j]]]
        K={x^(1<<a)^(1<<b) for a,b in itertools.combinations(free,2)}
        bounds=[];bad=0
        for missing in K:
            S=set(W)|(K-{missing})
            if missing in S or any(len(NB[v]&S)>2 for v in S):bad+=1;continue
            D={missing}|{q for q in range(512) if len(NB[q]&S)>=3}
            for v in S:
                if len(NB[v]&S)==2:D|=NB[v]-S
            if D&S:bad+=1;continue
            lower=0
            for c in W[4:9]:
                for q in NB[c]:
                    empty=sum({q,q^(1<<a),q^(1<<b),q^(1<<a)^(1<<b)}<=D for a,b in pairs)
                    degree=len(NB[q]-D);assert degree>0
                    lower+=12*empty//degree
            bounds.append(lower)
        trials.append(dict(position=j,branches=len(bounds),contradictions=bad,lower=min(bounds) if bounds else None))
    if trials:results.append(dict(edge=index,old=e['share_lower'],trials=trials))
out=dict(scope='Exploratory direct branch calculation only; no Lean proof for the count-conditioned case split yet.',results=results)
(HERE/'data/singleton-pilot.json').write_text(json.dumps(out,indent=2)+'\n')
print('Probed',len(results),'edges; all branches contradictory at',
      [r['edge'] for r in results if any(t['branches']==0 for t in r['trials'])])
