"""Verify exact proof receipts, manuscript evidence and saved checkpoint bytes."""
from pathlib import Path
import datetime,hashlib,json,re,subprocess,sys
H=Path(__file__).resolve().parents[1];R=H.parents[1]
read=lambda p:json.loads(Path(p).read_text(encoding='utf-8-sig'))
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
modules={'ActualInterval137':2,'BlockIntervals137':2,'PrefixCount137':7,
 'MissingCapacity137':1,'DegreeSum137':3,'Numeric137':2,'ActualBlocks137':1,
 'CountTwelve137':1,'ActualCount137':4}
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
paper_hash='8d98ae0a58e9e1748fe73bc78ca1786ee05415490a4cef7f6087228f24d885ad'
assert sha(paper)==sha(editor)==paper_hash
revision=read(H/'data/paper-revision.json');sourcecheck=read(H/'data/paper-source-review.json')
compile_result=read(H/'data/latex-compilation.json')
assert revision['after_sha256']==sourcecheck['source_sha256']==compile_result['source_sha256']==paper_hash
assert revision['new_named_definitions']==0 and revision['authors_and_preamble_unchanged']
assert sourcecheck['status']=='PASS_SOURCE_STRUCTURE_AND_UNCHANGED_WITNESS_APPENDIX'
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
 assert subprocess.check_output(g+['rev-parse','HEAD'],cwd=R,text=True).strip()=='120eb35cff441474aca79c4e38e2fb96e2ec9785'
 observation=read(H/'data/batch-observation.json')
 for row in observation['batches']:
  assert sha(H/row['snapshot'])==row['sha256']
  if 'checker_snapshot' in row:assert sha(H/row['checker_snapshot'])==row['checker_snapshot_sha256']
 verification=dict(status='PASS_ACTUAL_TWENTY_FOUR_WINDOW_BOUND',
  recorded_at=datetime.datetime.now(datetime.timezone.utc).isoformat(),modules=list(modules),
  axiom_reports=len(reports),checked_per_endpoint_common_neighbor_bound=12,
  checked_total_low_pair_window_bound=24,actual_occurrence_bound_lean_checked=True,
  boundary_free_eleven_checked=False,arbitrary_distance_only_assignment_checked=False,
  new_global_length_bound=False,sharpness_claimed=False,
  paper_revision=137,last_full_paper_revision=136,next_paper_revision=146,paper_sha256=paper_hash,
  paper_source_checks_passed=True,new_named_definitions=0,pdf_rebuilt=False,
  scope='Complete actual-snake low-pair occurrence bound24, with common-neighbour count12 per endpoint. Global length bound unchanged. Paper source checked; PDF compiler failed before TeX.')
 (H/'data/verification.json').write_text(json.dumps(verification,indent=2)+'\n',encoding='utf-8')
 checkpoint=dict(status=verification['status'],goal_status='ACTIVE',previous_goal_turn='PROGRESS',
  base_commit='120eb35cff441474aca79c4e38e2fb96e2ec9785',
  prior_checkpoint_sha256=sha(R/'milestones/136-intervals-and-paper/data/checkpoint.json'),
  verification_sha256=sha(H/'data/verification.json'),batch_observation_sha256=sha(H/'data/batch-observation.json'),
  repository_check_sha256=sha(H/'data/repository-check.json'),
  current_interval=[191,235],interval_scope='Maintained contributor result with incomplete independent upper-proof rebuild.',
  paper_revision=137,last_full_paper_revision=136,next_paper_revision=146,paper_sha256=paper_hash,pdf_rebuilt=False,
  selected_next_task='Investigate a necessary endpoint condition on the surviving seven-edge cycle, which has no012032 event; preserve proved-versus-conditional catalogue scope.')
 (H/'data/checkpoint.json').write_text(json.dumps(checkpoint,indent=2)+'\n',encoding='utf-8')
 selected={p for p in H.rglob('*') if p.is_file() and p!=manifest and '__pycache__' not in p.parts
  and p.suffix not in ['.tmp','.lock','.pending'] and p.name!='stage-paths.nul'}
 selected.update(R/n for n in ['README.md','COLLABORATION.md','RESEARCH_LEDGER.md','WORKSPACE.md',
  'milestones/README.md','handoff/README.md','handoff/CURRENT_STATUS.md','handoff/NEXT_AGENT_PROMPT.md',
  'paper/snake9_research.tex'])
 rows=[dict(path=p.relative_to(R).as_posix(),bytes=p.stat().st_size,sha256=sha(p)) for p in sorted(selected)]
 assert all(x['bytes']<100000000 for x in rows)
 manifest.write_text(json.dumps(dict(status='SAVED_ACTUAL_TWENTY_FOUR_AND_PAPER137',files=rows,
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
  if not n.startswith('milestones/137-actual-block-assembly/'):expected=expected.replace(b'\r\n',b'\n')
  assert b==expected,n
 proc.stdin.close();assert proc.wait()==0
print(json.dumps(dict(status='PASS_STAGED' if '--staged' in sys.argv else 'PASS_SAVED',files=len(names),
 bytes=sum(x['bytes'] for x in j['files'])+manifest.stat().st_size,axiom_reports=len(reports),
 checked_total_low_pair_window_bound=24,actual_occurrence_bound_lean_checked=True,
 new_global_length_bound=False,paper_revision=137,pdf_rebuilt=False)))
