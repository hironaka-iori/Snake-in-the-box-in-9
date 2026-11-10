from pathlib import Path
import json
H=Path('E:/Snake-in-a-box/milestones/187-clause-interpretation')
read=lambda p:json.loads(p.read_text(encoding='utf-8-sig'))
for p in (H/'data').glob('run-*.json'):
    assert read(p)['status']!='RUNNING',p
order=read(H/'data/current-order.json')
boundary=read(H/'data/boundary-order.json')
new=boundary+[x for x in order if x not in boundary]
(H/'data/current-order.json').write_text(json.dumps(new,indent=2)+'\n')
(H/'scripts/prioritize_boundary.py').write_bytes(Path(__file__).read_bytes())
print('Prioritized arithmetic modules; total planned',len(new))
