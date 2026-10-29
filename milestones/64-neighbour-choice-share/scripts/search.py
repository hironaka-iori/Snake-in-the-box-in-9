from pathlib import Path
import itertools,json,sys,time
HERE=Path(__file__).resolve().parents[1];ROOT=HERE.parents[1]
sys.path.insert(0,str(ROOT/'milestones/62-count-conditioned-share/scripts'))
from split_share import NB,forced,credit
graph=json.loads((ROOT/'milestones/63-long-window-splits/data/analysis.json').read_text())
rows=[];cache={};start=time.monotonic()
for i,e in enumerate(graph['edges']):
    ds=tuple(e['directions'])
    if ds not in cache:
        W=[0]
        for d in ds:W.append(W[-1]^(1<<d))
        C=W[6:11];D=forced(W);A=NB[W[0]]-set(W)-D;B=NB[W[-1]]-set(W)-D;branches=[]
        for a,b in itertools.product([None]+sorted(A),[None]+sorted(B)):
            T=set(W)|{v for v in [a,b] if v is not None}
            K=(A-({a} if a is not None else set()))|(B-({b} if b is not None else set()))
            if T&K or any(len(NB[v]&T)>2 for v in T):
                branches.append(dict(choices=[a,b],status='CONTRADICTION'));continue
            F=forced(T);absent=D|K|F
            assert not T&absent
            branches.append(dict(choices=[a,b],status='CREDIT',forced=sorted(F),absent=sorted(absent),
                mask=sum(1<<v for v in absent),lower=credit(C,absent)))
        lower=min(b['lower'] for b in branches if b['status']=='CREDIT')
        cache[ds]=dict(directions=list(ds),vertices=W,centres=C,A=sorted(A),B=sorted(B),D=sorted(D),branches=branches,lower=lower)
    rows.append(dict(edge=i,old=e['weight']-120*e['counts'][-1],**cache[ds]))
result=dict(rows=rows,unique_shapes=len(cache),seconds=time.monotonic()-start,
    scope='Complete neighbour-choice computation; local Lean proof and finite graph analysis are tracked separately. No global bound.')
(HERE/'data/choices.json').write_text(json.dumps(result,indent=2)+'\n')
positive=[r for r in rows if r['lower']>r['old']]
print('shapes',len(cache),'improved edges',len(positive),'branches needing certificate',sum(len(r['branches']) for r in positive),'seconds',result['seconds'])
print('cycle gains',[(i,rows[i]['old'],rows[i]['lower']) for i in graph['cycle'] if rows[i]['lower']>rows[i]['old']])
