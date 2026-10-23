"""Independent exact-square model checks for the six-centre hypothesis."""
import json,sys
from pathlib import Path
HERE=Path(__file__).resolve().parents[1];ROOT=HERE.parents[1]
sys.path.insert(0,str(ROOT/'milestones/28-direct-share-certificates/scripts'))
from direct import solve
shapes=json.loads((HERE/'data/six/shapes.json').read_text())
for index in [0,23,33]:
    case=dict(dirs=shapes[index],alpha=[[4,4]]*6)
    row=solve(case,20)
    (HERE/f'data/independent-six-{index}.json').write_text(json.dumps(row,indent=2)+'\n')
    print(index,row['status'],flush=True)
# A five-centre all-four window is the positive control; this is a local model.
row=solve(dict(dirs=[0,1,2,3,0,4],alpha=[[4,4]]*5),20)
(HERE/'data/independent-five-control.json').write_text(json.dumps(row,indent=2)+'\n')
print('five-centre-control',row['status'],flush=True)
