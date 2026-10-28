"""Exploratory complete neighbour choices at the ends of each saved cycle window."""
from pathlib import Path
import itertools,json,sys,time
HERE=Path(__file__).resolve().parents[1];ROOT=HERE.parents[1]
sys.path.insert(0,str(ROOT/'milestones/62-count-conditioned-share/scripts'))
from split_share import NB,forced,credit
rows=json.loads((HERE/'data/splits.json').read_text())['rows']
graph=json.loads((HERE/'data/analysis.json').read_text());out=[];start=time.monotonic()
for i in graph['cycle']:
    r=rows[i];W=r['vertices'];C=r['centres'];D=forced(W)
    A=NB[W[0]]-set(W)-D;B=NB[W[-1]]-set(W)-D;branches=[]
    for a,b in itertools.product([None]+sorted(A),[None]+sorted(B)):
        S=set(W)|{v for v in [a,b] if v is not None}
        absent=D|(A-({a} if a is not None else set()))|(B-({b} if b is not None else set()))
        if S&absent or any(len(NB[v]&S)>2 for v in S):
            branches.append(dict(choices=[a,b],status='DEGREE_CONTRADICTION'));continue
        absent|=forced(S)
        assert not S&absent
        branches.append(dict(choices=[a,b],status='CREDIT',lower=credit(C,absent)))
    lower=min(b['lower'] for b in branches if b['status']=='CREDIT')
    old=graph['edges'][i]['weight']-120*graph['edges'][i]['counts'][-1]
    out.append(dict(edge=i,old=old,lower=max(old,lower),branches=branches))
    print(i,old,max(old,lower),len(branches),flush=True)
result=dict(results=out,seconds=time.monotonic()-start,
    scope='Unproved complete neighbour-choice pilot on one recorded cycle. No Lean case-coverage proof or full-family evaluation; not included in certified weights.')
(HERE/'data/neighbour-pilot.json').write_text(json.dumps(result,indent=2)+'\n')
print('Total candidate gain',sum(r['lower']-r['old'] for r in out),'seconds',result['seconds'],flush=True)
