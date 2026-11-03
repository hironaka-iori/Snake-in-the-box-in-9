"""Freeze and verify this paper checkpoint, with optional exact staged-byte checks."""
from pathlib import Path
import hashlib,json,subprocess,sys
H=Path(__file__).resolve().parents[1];R=H.parents[1]
read=lambda p:json.loads(p.read_text(encoding='utf-8-sig'))
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
manifest=H/'data/file-manifest.json'
docs=['README.md','COLLABORATION.md','RESEARCH_LEDGER.md','WORKSPACE.md','milestones/README.md','handoff/README.md','handoff/CURRENT_STATUS.md','handoff/NEXT_AGENT_PROMPT.md','paper/snake9_research.tex']
v=read(H/'data/verification.json')
assert sha(R/'paper/snake9_research.tex')==v['paper_sha256']==sha(Path('D:/Codex/2026-10-13/new-chat/outputs/snake9_research.tex'))
for name,d in v['source_pins'].items():assert sha(R/name)==d,name
obs=read(H/'data/batch-observation.json')
for row in obs['batches']:
 assert sha(H/row['snapshot'])==row['sha256']
 assert row['pid']==row['process']['ProcessId'] and row['batch'] in row['process']['CommandLine']
 if 'checker_snapshot' in row:assert sha(H/row['checker_snapshot'])==row['checker_snapshot_sha256']
if '--verify' not in sys.argv and '--staged' not in sys.argv:
 assert not manifest.exists()
 prior=R/'milestones/125-critical-six-count/data/checkpoint.json'
 c=dict(status='PASS_PAPER126_SOURCE_AND_REUSED_MATHEMATICAL_EVIDENCE',base_commit='091b041b798f070de625fd6554b6f760cedeb646',previous_goal_turn='PROGRESS',goal_status='ACTIVE',prior_checkpoint=prior.relative_to(R).as_posix(),prior_checkpoint_sha256=sha(prior),verification_sha256=sha(H/'data/verification.json'),paper_revision=126,next_paper_revision=136,paper_sha256=v['paper_sha256'],new_definitions=0,new_global_bound=False,current_interval=[191,235],interval_scope='Prior maintained result; independent rebuild of contributor upper proof remains incomplete.',compiler_status='FAILED_BEFORE_TEX_WINDOWS_HELPER',batches=obs['batches'])
 (H/'data/checkpoint.json').write_text(json.dumps(c,indent=2)+'\n',encoding='utf-8')
 files=[p for p in H.rglob('*') if p.is_file() and p!=manifest and '__pycache__' not in p.parts]
 files += [R/name for name in docs]
 rows=[dict(path=p.relative_to(R).as_posix(),bytes=p.stat().st_size,sha256=sha(p)) for p in sorted(set(files))]
 assert all(row['bytes']<100000000 for row in rows)
 manifest.write_text(json.dumps(dict(status='SAVED_PAPER126_CHECKPOINT',files=rows,scope='Exact paper, previous-source archive, reviews, verification receipts, compiler error and continuation documents. Live verification trees and unrelated edits are excluded.'),indent=2)+'\n',encoding='utf-8')
j=read(manifest)
for row in j['files']:
 p=R/row['path'];assert p.stat().st_size==row['bytes'] and sha(p)==row['sha256'],row['path']
if '--staged' in sys.argv:
 names={row['path'] for row in j['files']}|{manifest.relative_to(R).as_posix()}
 cmd=['git','-c','core.commitGraph=false']
 actual=set(subprocess.check_output(cmd+['diff','--cached','--name-only','-z'],cwd=R).decode().strip('\0').split('\0'))
 assert actual==names,(actual-names,names-actual)
 for name in sorted(names):
  saved=(R/name).read_bytes();staged=subprocess.check_output(cmd+['show',':'+name],cwd=R)
  expected=saved if name.startswith('milestones/126-paper-revision/') else saved.replace(b'\r\n',b'\n')
  assert staged==expected,name
print(json.dumps(dict(status='PASS_STAGED' if '--staged' in sys.argv else 'PASS_SAVED',files=len(j['files'])+1,bytes=sum(r['bytes'] for r in j['files'])+manifest.stat().st_size,paper_sha256=v['paper_sha256'],new_definitions=0,goal='ACTIVE'),indent=2))
