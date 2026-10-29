"""Reduce certificate absence masks without changing any claimed bound."""
from pathlib import Path
import json,sys,time
HERE=Path(__file__).resolve().parents[1];ROOT=HERE.parents[1]
sys.path.insert(0,str(ROOT/'milestones/62-count-conditioned-share/scripts'))
from split_share import credit
rows=json.loads((HERE/'data/choices.json').read_text())['rows'];out=[];start=time.monotonic()
for r in rows:
    if r['lower']<=r['old']:continue
    cases=[]
    for br in r['branches']:
        if br['status']=='CONTRADICTION':cases.append(dict(choices=br['choices'],forced=[],mask=0));continue
        D=set(br['absent']);L=r['lower'];C=r['centres']
        for q in sorted(D,reverse=True):
            D.remove(q)
            if credit(C,D)<L:D.add(q)
        F=sorted(D&set(br['forced']))
        a,b=br['choices'];K=(set(r['A'])-({a} if a is not None else set()))|(set(r['B'])-({b} if b is not None else set()))
        assert D<=set(F)|K and credit(C,D)>=L
        cases.append(dict(choices=br['choices'],forced=F,mask=sum(1<<q for q in D),absent=sorted(D),lower=credit(C,D)))
    out.append(dict(edge=r['edge'],cases=cases))
    print(r['edge'],'mean mask size',sum(len(c.get('absent',[])) for c in cases)/len(cases),flush=True)
payload=dict(rows=out,seconds=time.monotonic()-start,scope='Certificate compression only; each reduced mask still supports the unchanged bound and must pass Lean checks.')
(HERE/'data/compact-certificates.json').write_text(json.dumps(payload,indent=2)+'\n')
print('Seconds',payload['seconds'],flush=True)
