"""Direct one-vertex share splits on every eleven-transition family window."""
from pathlib import Path
import json,sys,time
HERE=Path(__file__).resolve().parents[1];ROOT=HERE.parents[1]
sys.path.insert(0,str(ROOT/'milestones/62-count-conditioned-share/scripts'))
from split_share import NB,forced,credit
data=json.loads((ROOT/'milestones/62-count-conditioned-share/data/graph-analyses.json').read_text())
graph=next(g for g in data if g['length']==11)
cache={};rows=[];start=time.monotonic()
for i,e in enumerate(graph['edges']):
    ds=tuple(e['directions'])
    if ds not in cache:
        W=[0]
        for d in ds:W.append(W[-1]^(1<<d))
        C=W[6:11];D=forced(W);trials=[];best=None
        near=sorted(set.union(*(NB[v] for v in W))-set(W)-D)
        candidates=near+sorted(set(range(512))-set(W)-D-set(near))
        for q in candidates:
            D0=D|{q};a=credit(C,D0)
            if best is not None and a<=best['lower']:
                trials.append(dict(split=q,credit0=a,pruned_by=best['lower']))
                continue
            D1=forced(W+[q]);b=credit(C,D1)
            trial=dict(split=q,credit0=a,credit1=b,lower=min(a,b));trials.append(trial)
            if best is None or trial['lower']>best['lower']:
                best=dict(trial,absent0=sorted(D0),absent1=sorted(D1))
        assert best is not None
        cache[ds]=dict(directions=list(ds),vertices=W,centres=C,base=credit(C,D),trials=trials,**best)
    old=e['weight']-120*e['counts'][-1]
    rows.append(dict(edge=i,old=old,**cache[ds]))
out=dict(rows=rows,unique_shapes=len(cache),seconds=time.monotonic()-start,
    scope='All 512 vertices considered: known selected/absent vertices omitted; other splits either evaluated or pruned by their absent-branch upper bound on the minimum. Local improvements require Lean replay. No global bound.')
(HERE/'data/splits.json').write_text(json.dumps(out,indent=2)+'\n')
print('Shapes',len(cache),'improved edges',sum(r['lower']>r['old'] for r in rows),'seconds',out['seconds'])
print('Old cycle improvements',[(i,rows[i]['old'],rows[i]['lower']) for i in graph['cycle'] if rows[i]['lower']>rows[i]['old']])
