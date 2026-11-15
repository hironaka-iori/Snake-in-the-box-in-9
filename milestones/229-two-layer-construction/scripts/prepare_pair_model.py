"""Specialize the accepted lower-pair model to two upper/lower templates."""
from pathlib import Path
import json
H=Path(__file__).resolve().parents[1];R=H.parents[1]
s=(R/'milestones/227-shared-q8-construction/scripts/remaining_cp.py').read_text(encoding='utf-8')
reps=json.loads((H/'data/task-transfer.json').read_bytes())['pending']
start=s.index("ap.add_argument('--ids',default=");end=s.index(';a=ap.parse_args()',start)
s=s[:start]+"ap.add_argument('--ids',default="+repr(','.join(map(str,reps)))+")"+s[end:]
changes=[('data/remaining-companions.json','data/boundary-lower-pairs.json'),('data/regions44.json','data/regions46.json'),("first=p;second=", "first=c['first_upper_prefix']+p+c['first_upper_suffix'];second="),("(1 if z in anchors[k] else 2)","(0 if edges[k]==0 else 1 if z in anchors[k] else 2)")]
for old,new in changes:assert s.count(old)==1,(old,s.count(old));s=s.replace(old,new)
p=H/'scripts/pair_cp.py';assert not p.exists();p.write_text(s,encoding='utf-8')
runner=(R/'milestones/227-shared-q8-construction/scripts/run_remaining.py').read_text(encoding='utf-8').replace('remaining_cp.py','pair_cp.py').replace('data/remaining-companions.json','data/boundary-lower-pairs.json').replace('data/regions44.json','data/regions46.json')
(H/'scripts/run_pairs.py').write_text(runner,encoding='utf-8')
print('PREPARED',len(reps),'REDUCED_MODELS')
