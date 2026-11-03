"""Verify exact proof receipts, manuscript evidence and saved checkpoint bytes."""
from pathlib import Path
import datetime,hashlib,json,re,subprocess,sys
H=Path(__file__).resolve().parents[1];R=H.parents[1]
read=lambda p:json.loads(Path(p).read_text(encoding='utf-8-sig'))
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
modules={'IntervalBlocks136':5,'IntervalCount136':4,
         'ActualMissingSets136':1,'OutsideCount136':1}
reports=[]
for name,count in modules.items():
 q=read(H/'data'/(name+'-audit.json'))
 assert q['status']=='PASS' and q['exit_code']==0 and not q.get('timeout')
 source=H/'lean'/(name+'.lean');assert sha(source)==q['source_sha256']
 assert sha(Path(q['log']).parent/'source.lean.txt')==q['source_sha256']
 assert sha(Path(q['log']).parent/'checker.py.txt')==q['checker_sha256']
 for key in ['object','importable_object','log']:assert sha(q[key])==q[key+'_sha256']
 for n,d in q['dependencies'].items():
  p=Path(n);assert sha(p if p.is_absolute() else R/p)==d,n
 assert len(q['axioms'])==count
 assert all(set(x['axioms'])<={'propext','Classical.choice','Quot.sound'} for x in q['axioms'])
 assert not re.search(r'\b(sorry|admit|native_decide|axiom)\b',source.read_text(encoding='utf-8'))
 reports.extend(q['axioms'])
paper=R/'paper/snake9_research.tex'
editor=Path('D:/Codex/2026-10-13/new-chat/outputs/snake9_research.tex')
paper_hash='820820fafd255800cfe60f3c6cdde53dccc333ccaea2a49255299616458b1b0c'
assert sha(paper)==sha(editor)==paper_hash
revision=read(H/'data/paper-revision.json');sourcecheck=read(H/'data/paper-source-review.json')
compile_result=read(H/'data/latex-compilation.json')
assert revision['after_sha256']==sourcecheck['source_sha256']==compile_result['source_sha256']==paper_hash
assert revision['new_named_definitions']==0 and revision['authors_and_preamble_unchanged']
assert sourcecheck['status']=='PASS_SOURCE_STRUCTURE_AND_PRINTED_WITNESSES'
assert sourcecheck['balanced_braces_and_environments'] and not sourcecheck['pdf_rebuilt']
assert compile_result['status']=='INFRASTRUCTURE_FAILURE_BEFORE_TEX' and not compile_result['pdf_rebuilt']
assert sha(H/'audit/paper-before.tex.txt')==revision['before_sha256']
old=(H/'audit/paper-before.tex.txt').read_bytes();now=paper.read_bytes()
assert old.split(b'\\begin{document}',1)[0]==now.split(b'\\begin{document}',1)[0]
assert old.count(b'\\begin{definition}')==now.count(b'\\begin{definition}')
manifest=H/'data/file-manifest.json'
g=['git','-c','core.commitGraph=false','-c','maintenance.auto=false','-c','gc.auto=0']
if not manifest.exists():
 assert len(sys.argv)==1
 assert subprocess.check_output(g+['rev-parse','HEAD'],cwd=R,text=True).strip()=='61a7f80224433e4a576a955f85248accc0d515d9'
 observation=read(H/'data/batch-observation.json')
 for row in observation['batches']:
  assert sha(H/row['snapshot'])==row['sha256']
  if 'checker_snapshot' in row:assert sha(H/row['checker_snapshot'])==row['checker_snapshot_sha256']
 verification=dict(status='PASS_INTERVAL_AND_ACTUAL_MISSING_PAIR_COMPONENTS',
  recorded_at=datetime.datetime.now(datetime.timezone.utc).isoformat(),modules=list(modules),
  axiom_reports=len(reports),constructed_blocks_lean_checked=True,interval_count_lean_checked=True,
  actual_missing_pairs_lean_checked=True,outside_coordinate_partition_lean_checked=True,
  checked_per_endpoint_common_neighbor_bound=16,checked_total_low_pair_window_bound=32,
  written_per_endpoint_bound=12,written_total_bound=24,
  stronger_written_occurrence_bound_lean_checked=False,new_global_length_bound=False,
  paper_revision=136,next_paper_revision=146,paper_sha256=paper_hash,
  paper_source_checks_passed=True,new_named_definitions=0,pdf_rebuilt=False,
  scope='Checked interval and actual-pair components; full twelve-per-endpoint block assembly remains pending. Paper source checked, PDF compiler unavailable before TeX.')
 (H/'data/verification.json').write_text(json.dumps(verification,indent=2)+'\n',encoding='utf-8')
 checkpoint=dict(status=verification['status'],goal_status='ACTIVE',previous_goal_turn='PROGRESS',
  base_commit='61a7f80224433e4a576a955f85248accc0d515d9',
  prior_checkpoint_sha256=sha(R/'milestones/135-endpoint-count/data/checkpoint.json'),
  verification_sha256=sha(H/'data/verification.json'),batch_observation_sha256=sha(H/'data/batch-observation.json'),
  repository_check_sha256=sha(H/'data/repository-check.json'),
  current_interval=[191,235],interval_scope='Maintained contributor result with incomplete independent upper-proof rebuild.',
  paper_revision=136,next_paper_revision=146,paper_sha256=paper_hash,pdf_rebuilt=False,
  selected_next_task='Instantiate the constructed blocks in the actual snake, count the exceptional prefix once, sum the missing-degree estimates, and close the stronger endpoint occurrence count.')
 (H/'data/checkpoint.json').write_text(json.dumps(checkpoint,indent=2)+'\n',encoding='utf-8')
 selected={p for p in H.rglob('*') if p.is_file() and p!=manifest and '__pycache__' not in p.parts
  and p.suffix not in ['.tmp','.lock','.pending'] and p.name!='stage-paths.nul'}
 selected.update(R/n for n in ['README.md','COLLABORATION.md','RESEARCH_LEDGER.md','WORKSPACE.md',
  'milestones/README.md','handoff/README.md','handoff/CURRENT_STATUS.md','handoff/NEXT_AGENT_PROMPT.md',
  'paper/snake9_research.tex'])
 rows=[dict(path=p.relative_to(R).as_posix(),bytes=p.stat().st_size,sha256=sha(p)) for p in sorted(selected)]
 assert all(x['bytes']<100000000 for x in rows)
 manifest.write_text(json.dumps(dict(status='SAVED_INTERVAL_AND_PAPER136',files=rows,
  excluded_live_outputs='Other milestones remain live locally; frozen process-backed observations are included.'),indent=2)+'\n',encoding='utf-8')
j=read(manifest)
for x in j['files']:
 p=R/x['path'];assert p.stat().st_size==x['bytes'] and sha(p)==x['sha256'],x['path']
names={x['path'] for x in j['files']}|{manifest.relative_to(R).as_posix()}
if '--stage' in sys.argv:
 assert not subprocess.check_output(g+['diff','--cached','--name-only'],cwd=R).strip()
 p=H/'data/stage-paths.nul';p.write_bytes(b''.join(n.encode()+b'\0' for n in sorted(names)))
 subprocess.run(g+['add','-f','--pathspec-from-file='+str(p),'--pathspec-file-nul'],cwd=R,check=True)
if '--staged' in sys.argv:
 actual=set(subprocess.check_output(g+['diff','--cached','--name-only','-z'],cwd=R).decode().strip('\0').split('\0'));assert actual==names
 proc=subprocess.Popen(g+['cat-file','--batch'],cwd=R,stdin=subprocess.PIPE,stdout=subprocess.PIPE)
 for n in sorted(names):
  proc.stdin.write((':'+n+'\n').encode());proc.stdin.flush();header=proc.stdout.readline().decode().split();assert header[1]=='blob'
  b=proc.stdout.read(int(header[2]));assert proc.stdout.read(1)==b'\n'
  expected=(R/n).read_bytes()
  if not n.startswith('milestones/136-intervals-and-paper/'):expected=expected.replace(b'\r\n',b'\n')
  assert b==expected,n
 proc.stdin.close();assert proc.wait()==0
print(json.dumps(dict(status='PASS_STAGED' if '--staged' in sys.argv else 'PASS_SAVED',files=len(names),
 bytes=sum(x['bytes'] for x in j['files'])+manifest.stat().st_size,axiom_reports=len(reports),
 checked_total_low_pair_window_bound=32,stronger_written_occurrence_bound_lean_checked=False,
 new_global_length_bound=False,paper_revision=136,pdf_rebuilt=False)))
