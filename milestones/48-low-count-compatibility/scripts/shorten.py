"""Shorten the joint inequalities and asymmetric pair exclusions."""
from probe import p,HERE
import json
def canon(ds):
    names={};return [names.setdefault(d,len(names)) for d in ds]
answers=[]
for row in json.loads((HERE/'data/retained.json').read_text()):
    pos=[j+1 for j,c in enumerate(row['caps']) if c<21]
    if len(pos)!=2:continue
    phase=row['phase'];ds=row['directions'];caps=row['caps'];joint=phase in [8,3,9,7]
    cap=sum(caps[j-1] for j in pos)
    changed=True
    while changed:
        changed=False
        for side in ['left','right']:
            if side=='left' and min(pos)<2:continue
            if side=='right' and max(pos)>len(ds)-2:continue
            trial=canon(ds[1:] if side=='left' else ds[:-1]);newpos=[j-1 for j in pos] if side=='left' else pos
            newcaps=caps[1:] if side=='left' else caps[:-1];p.DIRS=trial
            result=p.solve(f'shorten-{phase}-{len(trial)}-{side}',[21]*len(newcaps) if joint else newcaps,seconds=2,joint=(newpos,cap) if joint else None)
            if result['status']=='UNSAT':ds=trial;pos=newpos;caps=newcaps;changed=True;break
    answer=dict(phase=phase,directions=ds,positions=pos,caps=caps,joint_cap=cap if joint else None)
    p.DIRS=ds
    result=p.solve(f'minimal-{phase}',[21]*len(caps) if joint else caps,seconds=3,joint=(pos,cap) if joint else None)
    answer['cycle_cuts']=result['cycle_cuts'];answers.append(answer);print('SHORT',{k:(len(v) if k=='cycle_cuts' else v) for k,v in answer.items()},flush=True)
(HERE/'data/shortened.json').write_text(json.dumps(answers,indent=2)+'\n')
