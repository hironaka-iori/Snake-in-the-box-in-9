"""Verify the completed proof, native evidence, manuscript and exact checkpoint bytes."""
from pathlib import Path
import datetime,hashlib,json,re,subprocess,sys
H=Path(__file__).resolve().parents[1];R=H.parents[1]
read=lambda p:json.loads(Path(p).read_text(encoding='utf-8-sig'))
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
completion=read(H/'data/proof-completion.json')
assert completion['status']=='PASS_ACTUAL_NINE_TRANSITION_EXCLUSION_AND_CONDITIONAL_ARITHMETIC'
assert len(completion['modules'])==16 and len(completion['axiom_reports'])==7
plan=read(H/'data/proof-plan-base.json')
assert sha(H/'data/proof-plan-base.json')==completion['proof_plan_sha256']
for n,d in plan['source_files_sha256'].items():assert sha(R/n)==d,n
for row in plan['artifacts']:assert sha(H/row['path'])==row['sha256']
for row in plan['export_artifacts']:assert sha(H/row['path'])==row['sha256']
for row in completion['modules']:
 p=H/row['receipt'];q=read(p);assert sha(p)==row['sha256']
 assert q['status'] in ['PASS','PASS_WINDOW_REPLAY_MODULE'] and q['exit_code']==0 and not q.get('timeout')
 name=row['module'];src=H/'lean'/(name.replace('.','/')+'.lean')
 assert sha(src)==q['source_sha256']
 assert not re.search(r'\b(sorry|admit|native_decide|axiom)\b',src.read_text(encoding='utf-8-sig'))
 if q['status']=='PASS':
  for key in ['object','importable_object','log']:assert sha(q[key])==q[key+'_sha256']
  log=Path(q['log']).parent
  assert sha(log/'source.lean.txt')==q['source_sha256']
  assert sha(log/'checker.py.txt')==q['checker_sha256']
  reports=q['axioms']
 else:
  assert sha(H/'build-base'/(name.replace('.','/')+'.olean'))==q['olean_sha256']
  assert sha(H/q['source_snapshot'])==q['source_sha256'] and sha(H/q['log'])==q['log_sha256']
  reports=q['theorem_audits']
 for n,d in q['dependencies'].items():
  p=Path(n);assert sha(p if p.is_absolute() else R/p)==d,n
 assert all(set(a['axioms'])<={'propext','Classical.choice','Quot.sound'} for a in reports)
base=read(H/'data/native-base.json');short=read(H/'data/replay-short.json')
assert base['status']==short['status']=='PASS_COMPLETE_NATIVE_RUP_REPLAY'
for mode,record in [('base',base),('short',short)]:
 w=H/('work/certificate-'+mode)
 for file,key in [('input.cnf','input_sha256'),('trimmed.lrat','trim_sha256'),('core-ids.json','core_ids_sha256')]:
  assert sha(w/file)==record[key]
assert (base['lemmas'],base['hints'])==(1340,106510)
assert (short['lemmas'],short['hints'])==(19338,2329967)
assert sha(H/'data/native-short.json')==short['native_record_sha256']
assert read(H/'data/closure-model-review.json')['status']=='PASS_NATIVE_SAT_MODEL_CHECK'
assert not read(H/'data/closure-model-review.json')['actual_snake']
cleanup=read(H/'data/overlay-cleanup.json');copies=read(H/'data/partial-module-overlay.json')
assert cleanup['files']==len(copies['files'])==1080
assert all(not Path(row['destination']).exists() for row in copies['files'])
paper=R/'paper/snake9_research.tex';editor=Path('D:/Codex/2026-10-13/new-chat/outputs/snake9_research.tex')
revision=read(H/'data/paper-revision.json');review=read(H/'data/paper-source-review.json')
assert sha(paper)==sha(editor)==revision['after_sha256']==review['source_sha256']
assert paper.read_bytes().split(b'\\begin{document}',1)[0]==(H/'audit/paper-before.tex.txt').read_bytes().split(b'\\begin{document}',1)[0]
assert revision['new_named_definitions']==0
assert read(H/'data/latex-compilation.json')['status']=='INFRASTRUCTURE_FAILURE_BEFORE_TEX'
obs=read(H/'data/batch-observation.json')
for row in obs['batches']:
 assert sha(H/row['snapshot'])==row['sha256']
 if 'checker_snapshot' in row:assert sha(H/row['checker_snapshot'])==row['checker_snapshot_sha256']
manifest=H/'data/file-manifest.json'
g=['git','-c','core.commitGraph=false','-c','maintenance.auto=false','-c','gc.auto=0']
if not manifest.exists():
 assert len(sys.argv)==1
 assert subprocess.check_output(g+['rev-parse','HEAD'],cwd=R,text=True).strip()=='9d24cbe7260ee87dd3d79b2e410d54527819f273'
 verification=dict(status=completion['status'],modules=16,axiom_reports=7,
  actual_nine_transition_exclusion_checked=True,short_upper_cap_exclusion_lean_checked=False,
  new_global_upper_bound=False,paper_sha256=sha(paper),new_named_definitions=0,pdf_rebuilt=False,
  final_source_sha256=sha(H/'lean/ActualBase138Minimal.lean'),
  proof_completion_sha256=sha(H/'data/proof-completion.json'),
  last_full_paper_revision=136,targeted_revision=138,next_full_paper_revision=146)
 (H/'data/verification.json').write_text(json.dumps(verification,indent=2)+'\n',encoding='utf-8')
 checkpoint=dict(status=completion['status'],goal_status='ACTIVE',previous_goal_turn='PROGRESS',
  base_commit='9d24cbe7260ee87dd3d79b2e410d54527819f273',
  prior_checkpoint_sha256=sha(R/'milestones/137-actual-block-assembly/data/checkpoint.json'),
  verification_sha256=sha(H/'data/verification.json'),current_interval=[191,235],
  interval_scope='Maintained contributor upper result with incomplete independent rebuild.',
  selected_next_task='Combine the proved full-nine deletion with the24-window allowance; first test uniform suffix credit83/3 and target mean3011/6, range<7753/6. Evaluate both distinct weight profiles.',
  paper_sha256=sha(paper),pdf_rebuilt=False,
  live_batch115_observed_completed=1017,live_batch115_total=1397)
 (H/'data/checkpoint.json').write_text(json.dumps(checkpoint,indent=2)+'\n',encoding='utf-8')
 selected={p for p in H.rglob('*') if p.is_file() and p!=manifest and '__pycache__' not in p.parts
  and p.suffix not in ['.tmp','.lock','.pending'] and p.name!='stage-paths.nul'}
 selected.update(R/n for n in ['README.md','COLLABORATION.md','RESEARCH_LEDGER.md','WORKSPACE.md',
  'milestones/README.md','handoff/README.md','handoff/CURRENT_STATUS.md','handoff/NEXT_AGENT_PROMPT.md','paper/snake9_research.tex'])
 rows=[dict(path=p.relative_to(R).as_posix(),bytes=p.stat().st_size,sha256=sha(p)) for p in sorted(selected)]
 assert all(x['bytes']<100000000 for x in rows)
 manifest.write_text(json.dumps(dict(status='SAVED_ACTUAL_NINE_EXCLUSION_AND_PAPER138',files=rows,
  excluded_live_outputs='Other milestones remain live. Only process-backed frozen observations are included. The unused duplicate dependency copies were removed; their source/hash inventory and cleanup receipt are retained.'),indent=2)+'\n',encoding='utf-8')
j=read(manifest)
for row in j['files']:
 p=R/row['path'];assert p.stat().st_size==row['bytes'] and sha(p)==row['sha256'],row['path']
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
  if not n.startswith('milestones/138-seven-cycle-endpoints/'):expected=expected.replace(b'\r\n',b'\n')
  assert b==expected,n
 proc.stdin.close();assert proc.wait()==0
print(json.dumps(dict(status='PASS_STAGED' if '--staged' in sys.argv else 'PASS_SAVED',
 files=len(names),bytes=sum(x['bytes'] for x in j['files'])+manifest.stat().st_size,
 modules=16,axiom_reports=7,actual_nine_transition_exclusion_checked=True,new_global_upper_bound=False)))
