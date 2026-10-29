"""Unproved joint-count propagation after neighbour choices on one attaining cycle."""
from pathlib import Path
import itertools,json,sys,time
HERE=Path(__file__).resolve().parents[1];ROOT=HERE.parents[1]
sys.path.insert(0,str(ROOT/'milestones/62-count-conditioned-share/scripts'))
from propagate import closure
from split_share import credit
rows=json.loads((HERE/'data/choices.json').read_text())['rows'];graph=json.loads((HERE/'data/analysis.json').read_text())
out=[];start=time.monotonic()
for i in graph['cycle']:
    r=rows[i];e=graph['edges'][i];W=r['vertices'];ds=r['directions'];cons=[]
    for k,b in enumerate(e['counts']):
        j=k+5;free=set(range(9))-{ds[j-1],ds[j]}
        K=sorted(W[j]^(1<<a)^(1<<b) for a,b in itertools.combinations(sorted(free),2))
        cons.append(dict(position=j,corners=K,lo=b,hi=21 if b==6 else b))
    branches=[]
    for br in r['branches']:
        if br['status']=='CONTRADICTION':continue
        S=set(W)|{v for v in br['choices'] if v is not None};D=set(br['absent'])
        value=closure(W,cons,seed=(S,D))
        if value['status']=='CLOSED':value['lower']=credit(r['centres'],set(value['absent']))
        branches.append(dict(choices=br['choices'],**value))
    survivors=[b for b in branches if b['status']=='CLOSED']
    old=e['weight']-120*e['counts'][-1]
    value=dict(edge=i,counts=e['counts'],constraints=cons,old=old,
        lower=max(old,min(b['lower'] for b in survivors)) if survivors else None,branches=branches)
    out.append(value);print(i,old,value['lower'],'surviving branches',len(survivors),'/',len(branches),flush=True)
payload=dict(results=out,seconds=time.monotonic()-start,
    scope='Unproved joint-count deductions on one candidate attaining cycle. No Lean replay, complete-family evaluation or change to certified weights.')
(HERE/'data/count-pilot.json').write_text(json.dumps(payload,indent=2)+'\n');print('Seconds',payload['seconds'],flush=True)
