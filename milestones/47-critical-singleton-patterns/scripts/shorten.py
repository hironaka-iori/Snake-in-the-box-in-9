"""Minimize the transition context of each count-one exclusion."""
from probe import p,HERE,rows
import json
def canon(ds):
    names={};return [names.setdefault(d,len(names)) for d in ds]
answers=[]
for phase in [0,2,3,8,9,10]:
    ds=rows[phase]['directions'];j=rows[phase]['counts'].index(1)+1
    changed=True
    while changed:
        changed=False
        for side in ['left','right']:
            if side=='left' and j<2:continue
            if side=='right' and j>len(ds)-2:continue
            trial=canon(ds[1:] if side=='left' else ds[:-1]);k=j-1 if side=='left' else j
            caps=[21]*(len(trial)-1);caps[k-1]=1;p.DIRS=trial
            out=p.solve(f'shorten-{phase}-{len(trial)}-{side}',caps,seconds=2)
            if out['status']=='UNSAT':ds=trial;j=k;changed=True;break
    caps=[21]*(len(ds)-1);caps[j-1]=1;p.DIRS=ds
    out=p.solve(f'minimal-{phase}',caps,seconds=3)
    answer=dict(phase=phase,directions=ds,position=j,caps=caps,cycle_cuts=out['cycle_cuts'])
    answers.append(answer);print('MINIMAL',answer,flush=True)
(HERE/'data/minimal-patterns.json').write_text(json.dumps(answers,indent=2)+'\n')
