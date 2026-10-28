"""One Boolean split, retaining empty-square credit in both alternatives."""
from pathlib import Path
import json,itertools,time
HERE=Path(__file__).resolve().parents[1];ROOT=HERE.parents[1]
NB=[{x^(1<<d) for d in range(9)} for x in range(512)]
NMS=[sum(1<<v for v in ns) for ns in NB]
FM=[[sum(1<<v for v in (q,q^(1<<a),q^(1<<b),q^(1<<a)^(1<<b)))
     for a,b in itertools.combinations(range(9),2)] for q in range(512)]
def forced(W):
    W=set(W)
    assert all(len(NB[v]&W)<=2 for v in W)
    D={q for q in range(512) if len(NB[q]&W)>=3}
    for v in W:
        if len(NB[v]&W)==2:D|=NB[v]-W
    assert not D&W
    return D
def credit(C,D):
    mask=sum(1<<q for q in D)
    z=0
    for c in C:
        for q in NB[c]:
            den=9-(NMS[q]&mask).bit_count();assert den>0
            z+=12*sum(f&mask==f for f in FM[q])//den
    return z
def main():
    edges=json.loads((ROOT/'milestones/61-critical-family-share/data/critical-edges.json').read_text())
    cache={};rows=[];start=time.monotonic()
    for i,e in enumerate(edges):
        ds=tuple(e['directions'])
        if ds not in cache:
            W=[0]
            for d in ds:W.append(W[-1]^(1<<d))
            C=W[4:9];D=forced(W);trials=[]
            for q in sorted(set.union(*(NB[v] for v in W))-set(W)-D):
                D0=D|{q};D1=forced(W+[q])
                a,b=credit(C,D0),credit(C,D1)
                trials.append(dict(split=q,absent0=sorted(D0),absent1=sorted(D1),credit0=a,credit1=b,lower=min(a,b)))
            best=max(trials,key=lambda t:t['lower'])
            cache[ds]=dict(directions=list(ds),vertices=W,centres=C,base=credit(C,D),trials=trials,**best)
        rows.append(dict(edge=i,old=e['share_lower'],**cache[ds]))
    payload=dict(rows=rows,unique_shapes=len(cache),seconds=time.monotonic()-start,
       scope='Candidate geometric bounds, one selected-vertex split, no count premises. Lean replay required.')
    (HERE/'data/split-share.json').write_text(json.dumps(payload,indent=2)+'\n')
    print('Shapes',len(cache),'improved edges',sum(r['lower']>r['old'] for r in rows),'seconds',payload['seconds'])
    print([(r['edge'],r['old'],r['lower'],r['split']) for r in rows if r['lower']>r['old']])
if __name__=='__main__':main()
