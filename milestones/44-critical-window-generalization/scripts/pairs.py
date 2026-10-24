"""Test shorter direction windows and candidate joint count inequalities."""
from probe import p,HERE
import json
records=[]
for name,ds,positions in [
    ('four-step',[0,1,2,3,4,2],[1,5]),
    ('five-step',[0,1,2,3,4,2,0],[1,6]),
    ('full-phase2',[0,1,2,3,4,0,3,1],[2,6]),
    ('full-phase8',[0,1,2,0,3,4,0,1],[2,7])]:
    p.DIRS=ds;caps=[21]*(len(ds)-1)
    for j in positions:caps[j-1]=3
    records.append(p.solve(name+'-3-3',caps,seconds=3))
    for bound in [6,7,8,9,10]:
        records.append(p.solve(name+'-sum-'+str(bound),[21]*(len(ds)-1),seconds=3,joint=(positions,bound)))
(HERE/'data/pair-survey.json').write_text(json.dumps(records,indent=2)+'\n')
