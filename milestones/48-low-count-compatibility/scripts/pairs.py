"""Replace coordinatewise low-count caps by a joint inequality where possible."""
from probe import p,HERE
import json
out=[]
for r in json.loads((HERE/'data/retained.json').read_text()):
    pos=[j+1 for j,c in enumerate(r['caps']) if c<21]
    if len(pos)!=2:continue
    p.DIRS=r['directions']
    for cap in range(sum(r['caps'][j-1] for j in pos),11):
        result=p.solve(f'pair-{r["phase"]}-sum-{cap}',[21]*7,seconds=3,joint=(pos,cap))
        out.append(dict(phase=r['phase'],positions=pos,cap=cap,status=result['status'],cycle_cuts=len(result['cycle_cuts'])))
        if result['status']=='SAT':break
(HERE/'data/pair-boundaries.json').write_text(json.dumps(out,indent=2)+'\n')
