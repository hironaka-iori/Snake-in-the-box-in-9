"""Verify and freeze completed140 evidence without publishing regenerated build objects."""
from pathlib import Path
import hashlib,json,os,re,subprocess,sys
H=Path(__file__).resolve().parents[1];R=H.parents[1]
read=lambda p:json.loads(Path(p).read_text(encoding='utf-8-sig'))
def sha(p):
 d=hashlib.sha256()
 with Path(p).open('rb') as f:
  for b in iter(lambda:f.read(1048576),b''):d.update(b)
 return d.hexdigest()
proof=read(H/'data/proof-completion.json');assert proof['status']=='PASS_ACTUAL_012032_WEAK_EXCLUSION' and proof['modules']==123
assert len(proof['receipts'])==123 and len(proof['actual_and_weak_axiom_reports'])==11
for row in proof['receipts']:
 path=R/row['path'];assert sha(path)==row['sha256']
 q=read(path);assert q['exit_code']==0 and not q.get('timeout',False)
 source=H/'lean'/(row['module'].replace('.','/')+'.lean');assert sha(source)==q['source_sha256']
 for p,d in q['dependencies'].items():assert sha(Path(p) if Path(p).is_absolute() else R/p)==d,p
 if q['status']=='PASS_WINDOW_REPLAY_MODULE':
  assert sha(H/'build-base'/(row['module'].replace('.','/')+'.olean'))==q['olean_sha256']
  assert sha(H/q['log'])==q['log_sha256'] and sha(H/q['source_snapshot'])==q['source_sha256']
  reports=q['theorem_audits']
 else:
  assert q['status']=='PASS'
  for key in ['object','importable_object','log']:assert sha(q[key])==q[key+'_sha256']
  reports=q['axioms']
 assert all(set(x['axioms'])<={'propext','Classical.choice','Quot.sound'} for x in reports)
q=read(H/'data/ZeroCredit140-audit.json');assert q['status']=='PASS' and q['exit_code']==0 and len(q['axioms'])==2
assert sha(H/'lean/ZeroCredit140.lean')==q['source_sha256']
for key in ['object','importable_object','log']:assert sha(q[key])==q[key+'_sha256']
for p,d in q['dependencies'].items():assert sha(Path(p) if Path(p).is_absolute() else R/p)==d,p
native=read(H/'data/native-base.json');assert native['status']=='PASS_COMPLETE_NATIVE_RUP_REPLAY'
assert (native['lemmas'],native['hints'],native['core_clauses'])==(18606,1397536,4163)
for p,d in native['source_files_sha256'].items():assert sha(R/p)==d,p
for p,d in native['preserved_files_sha256'].items():assert sha(H/'work/certificate-base'/p)==d,p
plan=read(H/'data/proof-plan-base.json');assert len(plan['module_order'])==121
for row in plan['artifacts']+plan['export_artifacts']:assert sha(H/row['path'])==row['sha256'],row['path']
for p,d in plan['source_files_sha256'].items():assert sha(R/p)==d,p
assert read(H/'data/independent-semantics.json')['status']=='PASS_INDEPENDENT_ENCODING_AND_CORE_AUDIT'
prep=read(H/'data/graph-preparation.json');assert prep['status']=='PREPARED_NOT_EXECUTED_PROOF_REQUIRED'
assert sha(H/'scripts/prepare_graph.py')==prep['prepare_sha256'] and sha(H/'scripts/evaluate_graph.py')==prep['evaluate_sha256']
assert not (H/'data/five-cycle-credit83').exists()
assert read(H/'data/saved-cycle-positions.json')['completed_exact_edges']==[308566,3806548]
assert not re.search(r'\b(sorry|admit|native_decide|axiom)\b','\n'.join(p.read_text(encoding='utf-8') for p in (H/'lean').rglob('*.lean')))
progress=read(H/'data/replay-progress-base.json');assert progress['active'] is None and len(progress['checked_modules'])==120
assert progress['status']=='STOPPED' and 'Mathlib.Tactic' in progress['exception']
paper=R/'paper/snake9_research.tex';editor=Path('D:/Codex/2026-10-13/new-chat/outputs/snake9_research.tex')
review=read(H/'data/paper-source-review.json');revision=read(H/'data/paper-revision.json')
assert sha(paper)==sha(editor)==review['source_sha256']==revision['after_sha256']
assert paper.read_bytes().split(b'\\begin{document}',1)[0]==(H/'audit/paper-before.tex.txt').read_bytes().split(b'\\begin{document}',1)[0]
assert review['definition_environment_count']==1 and revision['new_named_definitions']==0
compile=read(H/'data/latex-compilation.json');assert compile['source_sha256']==sha(paper)
for row in read(H/'data/batch-observation.json')['batches']:
 assert sha(H/row['snapshot'])==row['sha256']
 if 'checker_snapshot' in row:assert sha(H/row['checker_snapshot'])==row['checker_snapshot_sha256']
g=['git','-c','core.commitGraph=false','-c','maintenance.auto=false','-c','gc.auto=0']
manifest=H/'data/file-manifest.json'
if not manifest.exists():
 assert len(sys.argv)==1
 assert subprocess.check_output(g+['rev-parse','HEAD'],cwd=R,text=True).strip()=='8cc94035c72589d8d70edc31c576260d0cbef1d0'
 verification=dict(status='PASS_ACTUAL_FIVE_COUNT_EXCLUSION_AND_ZERO_CREDIT_ARITHMETIC',actual_proof_modules=123,separate_arithmetic_modules=1,final_semantic_and_actual_axiom_reports=11,arithmetic_axiom_reports=2,
  new_global_upper_bound=False,full_graph_executed=False,weak_bounds=[[3,3],[0,5],[4,4],[0,5],[3,3]],paper_sha256=sha(paper),new_named_definitions=0,pdf_rebuilt=compile['pdf_rebuilt'])
 (H/'data/verification.json').write_text(json.dumps(verification,indent=2)+'\n',encoding='utf-8')
 checkpoint=dict(status=verification['status'],goal_status='ACTIVE',previous_goal_turn='PROGRESS',base_commit='8cc94035c72589d8d70edc31c576260d0cbef1d0',prior_checkpoint_sha256=sha(R/'milestones/139-exclusion-occurrence-credit/data/checkpoint.json'),verification_sha256=sha(H/'data/verification.json'),
 current_interval=[191,235],interval_scope='Maintained contributor upper proof with incomplete independent rebuilding.',selected_next_task='Zero occurrence credit after the checked weak012032 exclusion; evaluate both profiles. Mean496 and range<632 would yield comparison<235.',
 last_full_paper_revision=136,targeted_paper_revision=140,next_full_paper_revision=146,paper_sha256=sha(paper),pdf_rebuilt=compile['pdf_rebuilt'],live115_observed_modules=1095,total115_modules=1397)
 (H/'data/checkpoint.json').write_text(json.dumps(checkpoint,indent=2)+'\n',encoding='utf-8')
 selected=set()
 for folder,dirs,files in os.walk(H,followlinks=False):
  dirs[:]=[n for n in dirs if not n.startswith('build') and n!='__pycache__']
  for name in files:
   p=Path(folder)/name
   if p==manifest or p.suffix in ['.tmp','.pending','.lock'] or name=='stage-paths.nul':continue
   selected.add(p)
 selected.update(R/n for n in ['README.md','COLLABORATION.md','RESEARCH_LEDGER.md','WORKSPACE.md','milestones/README.md','handoff/README.md','handoff/CURRENT_STATUS.md','handoff/NEXT_AGENT_PROMPT.md','paper/snake9_research.tex'])
 rows=[dict(path=p.relative_to(R).as_posix(),bytes=p.stat().st_size,sha256=sha(p)) for p in sorted(selected)]
 assert all(x['bytes']<100000000 for x in rows)
 manifest.write_text(json.dumps(dict(status='SAVED_ACTUAL_WINDOW_THEOREM_AND_PAPER140',files=rows,excluded='Regenerated build objects remain local with hashes in receipts. Other milestones remain live; frozen observations only.'),indent=2)+'\n',encoding='utf-8')
j=read(manifest)
for row in j['files']:
 p=R/row['path'];assert p.stat().st_size==row['bytes'] and sha(p)==row['sha256'],row['path']
names={row['path'] for row in j['files']}|{manifest.relative_to(R).as_posix()}
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
  if not n.startswith('milestones/140-five-cycle-window/'):expected=expected.replace(b'\r\n',b'\n')
  assert b==expected,n
 proc.stdin.close();assert proc.wait()==0
print(json.dumps(dict(status='PASS_STAGED' if '--staged' in sys.argv else 'PASS_SAVED',files=len(names),bytes=sum(x['bytes'] for x in j['files'])+manifest.stat().st_size,actual_proof_modules=123,arithmetic_modules=1,new_global_upper_bound=False)))
