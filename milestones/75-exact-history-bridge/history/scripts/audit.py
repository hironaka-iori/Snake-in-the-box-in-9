"""Recheck saved successful proof receipts without launching Lean."""
from pathlib import Path
import hashlib,json,re
HERE=Path(__file__).resolve().parents[1]
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
read=lambda p:json.loads(p.read_text(encoding='utf-8'))
proof=read(HERE/'data/proof-audit.json')
assert proof['status']=='PASS_EXACT_HISTORY'
assert sha(HERE/'data/source-provenance.json')==proof['provenance_sha256']
sources=read(HERE/'data/source-provenance.json')
for row in sources['sources']:assert sha(Path(row['path']))==row['sha256']
assert sha(HERE/'lean/ExactHistory.lean')==sources['source_sha256']
count=0
for row in proof['records']:
    name=row['module'];source=HERE/'lean'/(name+'.lean');log=HERE/'logs'/(name+'.log')
    assert row['exit_code']==0
    assert sha(source)==row['source_sha256']
    assert sha(log)==row['log_sha256']
    assert sha(HERE/'build'/(name+'.olean'))==row['olean_sha256']
    assert not re.search(r'\b(sorry|admit|native_decide)\b',source.read_text(encoding='utf-8'))
    assert not any(s in log.read_text(encoding='utf-8') for s in ['error:','sorryAx'])
    assert source.read_text(encoding='utf-8').count('#print axioms')==len(row['theorems'])
    for theorem in row['theorems']:
        assert set(theorem['axioms'])<={'propext','Classical.choice','Quot.sound'}
    count+=len(row['theorems'])
assert count==22
out=dict(status='PASS_SAVED_HISTORY_AUDIT',theorems=count,proof_receipt_sha256=sha(HERE/'data/proof-audit.json'),scripts={p.name:sha(p) for p in sorted((HERE/'scripts').glob('*.py'))},readme_sha256=sha(HERE/'README.md'))
(HERE/'data/saved-audit.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
print(out['status'],count,'checked declarations.')
