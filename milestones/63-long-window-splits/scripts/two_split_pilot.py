"""Unproved depth-two pilot on the saved attaining cycle; no certified weights changed."""
from pathlib import Path
import json,sys,time
HERE=Path(__file__).resolve().parents[1];ROOT=HERE.parents[1]
sys.path.insert(0,str(ROOT/'milestones/62-count-conditioned-share/scripts'))
from split_share import forced,credit
rows=json.loads((HERE/'data/splits.json').read_text())['rows']
graph=json.loads((HERE/'data/analysis.json').read_text())
def second(W,D,C):
    best=dict(lower=credit(C,D),split=None)
    for q in sorted(set(range(512))-set(W)-D):
        D0=D|{q};a=credit(C,D0)
        if a<=best['lower']:continue
        D1=D|forced(W+[q]);b=credit(C,D1)
        if min(a,b)>best['lower']:
            best=dict(split=q,lower=min(a,b),credit0=a,credit1=b,absent0=sorted(D0),absent1=sorted(D1))
    return best
results=[];start=time.monotonic()
for i in graph['cycle']:
    r=rows[i];W=r['vertices'];C=r['centres'];q=r['split']
    b0=second(W,set(r['absent0']),C);b1=second(W+[q],set(r['absent1']),C)
    lower=min(b0['lower'],b1['lower']);old=graph['edges'][i]['weight']-120*graph['edges'][i]['counts'][-1]
    results.append(dict(edge=i,old=old,lower=max(old,lower),root_split=q,branches=[b0,b1]))
    print(i,old,max(old,lower),flush=True)
out=dict(results=results,seconds=time.monotonic()-start,
    scope='Unproved depth-two pilot on one attaining cycle, retaining the previously selected first split. No Lean certificate, complete family evaluation or new graph-bound claim.')
(HERE/'data/two-split-pilot.json').write_text(json.dumps(out,indent=2)+'\n')
print('Total candidate gain',sum(r['lower']-r['old'] for r in results),'seconds',out['seconds'],flush=True)
