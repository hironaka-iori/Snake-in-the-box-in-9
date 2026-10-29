"""Joint-count propagation on every complete neighbour-choice family window."""
from pathlib import Path
import itertools,json,sys,time,collections
HERE=Path(__file__).resolve().parents[1];ROOT=HERE.parents[1]
sys.path.insert(0,str(ROOT/'milestones/62-count-conditioned-share/scripts'))
from propagate import closure
from split_share import credit
rows=json.loads((ROOT/'milestones/64-neighbour-choice-share/data/choices.json').read_text())['rows']
graph=json.loads((ROOT/'milestones/64-neighbour-choice-share/data/analysis.json').read_text());out=[];start=time.monotonic()
for i,(r,e) in enumerate(zip(rows,graph['edges'])):
    W=r['vertices'];ds=r['directions'];cons=[]
    for k,b in enumerate(e['counts']):
        j=k+5;free=set(range(9))-{ds[j-1],ds[j]}
        K=sorted(W[j]^(1<<a)^(1<<b) for a,b in itertools.combinations(sorted(free),2))
        cons.append(dict(position=j,corners=K,lo=b,hi=21 if b==6 else b))
    branches=[]
    for br in r['branches']:
        assert br['status']=='CREDIT'
        S=set(W)|{v for v in br['choices'] if v is not None};D=set(br['absent'])
        value=closure(W,cons,seed=(S,D))
        if value['status']=='CLOSED':value['lower']=credit(r['centres'],set(value['absent']))
        branches.append(dict(choices=br['choices'],initial_selected=sorted(S),initial_absent=sorted(D),**value))
    survivors=[b for b in branches if b['status']=='CLOSED'];old=e['weight']-120*e['counts'][-1]
    lower=max(old,min(b['lower'] for b in survivors)) if survivors else None
    payload=dict(edge=i,directions=ds,vertices=W,centres=r['centres'],A=r['A'],B=r['B'],counts=e['counts'],constraints=cons,old=old,lower=lower,branches=branches,
        scope='Recorded count-conditioned deductions. No Lean-checked claim until replay and geometric interpretation pass.')
    (HERE/f'data/cases/e{i:03d}.json').write_text(json.dumps(payload,indent=2)+'\n')
    out.append(dict(edge=i,old=old,lower=lower,surviving_branches=len(survivors),branches=len(branches)))
summary=dict(results=out,seconds=time.monotonic()-start,excluded_candidates=[r['edge'] for r in out if r['lower'] is None],
    improved_candidates=[r['edge'] for r in out if r['lower'] is not None and r['lower']>r['old']],
    scope='Exploratory full-family deductions; no new certified graph weights or global bound.')
(HERE/'data/summary.json').write_text(json.dumps(summary,indent=2)+'\n');print({k:v for k,v in summary.items() if k!='results'})
