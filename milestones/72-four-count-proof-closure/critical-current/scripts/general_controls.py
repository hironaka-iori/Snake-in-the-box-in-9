"""Independent CP-SAT tests for unconditioned one-centre and five-centre shares."""
from pathlib import Path
import json,sys
HERE=Path(__file__).resolve().parents[1];ROOT=HERE.parents[2]
sys.path.insert(0,str(ROOT/'milestones/28-direct-share-certificates/scripts'));import direct
for ds,cap in [([0,1],0),([0,1],5),([0,1],11),([0,1,2,3,4,5],0),([0,1,2,0,3,2],0)]:
 case=dict(dirs=ds,alpha=[(0,21)]*(len(ds)-1),cap=cap)
 result=direct.solve(case,seconds=10);tag=''.join(map(str,ds))
 (HERE/f'data/control-{tag}-{cap}.json').write_text(json.dumps(result,indent=2)+'\n');print(tag,cap,result['status'],result.get('census',{}).get('total_share'),flush=True)
