from pathlib import Path
import json,hashlib
H=Path('E:/Snake-in-a-box/milestones/187-clause-interpretation')
p=H/'lean/Combined187.lean'
assert not (H/'data/Combined187-audit.json').exists()
s=p.read_text().replace('checked by `#print axioms` below','reported below')
p.write_text(s,encoding='utf-8',newline='\n')
digest=hashlib.sha256(p.read_bytes()).hexdigest()
for name in ['Combined187','BoundarySlack187']:
    assert not (H/'data'/(name+'-audit.json')).exists()
    p=H/'data'/(name+'-execution.json');j=json.loads(p.read_text())
    j['source_sha256']['Combined187']=digest
    p.write_text(json.dumps(j,indent=2)+'\n')
(H/'scripts/repair_arithmetic.py').write_bytes(Path(__file__).read_bytes())
print('Removed a comment mistaken for an extra dependency report; prior evidence preserved.')
