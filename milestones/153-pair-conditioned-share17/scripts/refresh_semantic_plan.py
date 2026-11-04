"""Record a source-level signature repair before any153 Lean invocation."""
from pathlib import Path
import hashlib,json
H=Path(__file__).resolve().parents[1]
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
path=H/'data/semantic-source-plan.json';old=path.read_bytes();plan=json.loads(old)
assert plan['checked'] is False
assert not list((H/'data').glob('*-audit.json'))
for row in plan['artifacts']:
    p=H/row['path'];row.update(sha256=sha(p),bytes=p.stat().st_size)
plan['source_files_sha256'][str(H/'scripts/prepare_semantics.py')]=sha(H/'scripts/prepare_semantics.py')
plan['source_revision']='Correct AxiomsS argument order and rewrite centresOf to centresK, matching the checked150 assembly. Original unchecked source is preserved in audit/semantic-source-v1.'
path.write_text(json.dumps(plan,indent=2)+'\n',encoding='utf-8')
out=dict(status='PASS_SOURCE_SIGNATURE_REPAIR_UNCOMPILED',previous_plan_sha256=hashlib.sha256(old).hexdigest(),
    current_plan_sha256=sha(path),Lean_started=False,script_sha256=sha(Path(__file__)))
(H/'data/semantic-source-repair.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
print(json.dumps(out))
