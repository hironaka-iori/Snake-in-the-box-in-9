from pathlib import Path
import json,sys
HERE=Path(__file__).resolve().parents[1];ROOT=HERE.parents[1]
sys.path.insert(0,str(ROOT/'milestones/55-critical-share-family/scripts'))
from cover import find_cycle
rows=json.loads((HERE/'data/windows.json').read_text());edges=json.loads((HERE/'data/critical-edges.json').read_text())
assert find_cycle(edges,set()) is not None
alone=[];witnesses={}
for i,row in enumerate(rows):
    cycle=find_cycle(edges,{i})
    if cycle is None:alone.append(i)
    else:witnesses[i]=cycle
priority=alone+[i for i in range(len(rows)) if i not in alone]
out=dict(single_pattern_cycle_covers=alone,priority=priority,remaining_cycle_witnesses=witnesses,
    scope='Finite critical graph only; no positive share bound is assumed or proved by coverage.')
(HERE/'data/priorities.json').write_text(json.dumps(out,indent=2)+'\n')
print({k:v for k,v in out.items() if k!='remaining_cycle_witnesses'})
