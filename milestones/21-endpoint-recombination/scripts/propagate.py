"""Degree propagation inside parent unions with their intersection retained."""
import json
from collections import Counter
from exchange import HERE,parents,transforms,sha
from pathlib import Path
NEIGH=[{v^(1<<k) for k in range(9)} for v in range(512)]
def closure(a,b):
    allowed=set(a)|set(b);forced=set(a)&set(b);trace=[]
    while True:
        old=(len(allowed),len(forced))
        for v in sorted(allowed):
            if v not in allowed:continue
            target=1 if v in (41,67) else 2
            f=NEIGH[v]&forced;t=NEIGH[v]&allowed
            if v in forced:
                assert len(f)<=target<=len(t)
                if len(f)==target:
                    gone=t-f
                    if gone:allowed-=gone;trace.append(['remove_neighbors',v,sorted(gone)])
                if len(t)==target:
                    add=t-forced
                    if add:forced|=add;trace.append(['force_neighbors',v,sorted(add)])
            elif len(f)>target or len(t)<target:
                allowed.remove(v);trace.append(['remove_vertex',v])
        assert forced<=allowed
        assert set(a)<=allowed and set(b)<=allowed
        assert forced<=set(a) and forced<=set(b)
        if old==(len(allowed),len(forced)):break
    return {'allowed':sorted(allowed),'forced':sorted(forced),'trace':trace}
def main():
    a,b=parents();rows=[]
    for i,(_,_,q) in enumerate(transforms(b)):
        r=closure(a,q);rows.append({'alignment':i,'allowed_count':len(r['allowed']),'forced_count':len(r['forced'])})
    out={'script_sha256_lf':sha(Path(__file__)),'rows':rows,'allowed_histogram':dict(Counter(r['allowed_count'] for r in rows)),'observation':'Both full parent paths remain feasible throughout, so propagation cannot delete any vertex of their union. This is a control, not an exclusion.'}
    (HERE/'data/propagation-control.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
    print(json.dumps(out['allowed_histogram']))
if __name__=='__main__':main()
