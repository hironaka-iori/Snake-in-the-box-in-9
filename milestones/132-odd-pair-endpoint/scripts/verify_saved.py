"""Verify the complete endpoint theorem and freeze its exact evidence."""
from pathlib import Path
import datetime,hashlib,json,re,subprocess,sys
H=Path(__file__).resolve().parents[1];R=H.parents[1]
read=lambda p:json.loads(Path(p).read_text(encoding='utf-8-sig'))
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
allowed={'propext','Classical.choice','Quot.sound'}
def pins(rows,base=R):
 for n,d in rows.items():
  p=Path(n);assert sha(p if p.is_absolute() else base/p)==d,n
native=read(H/'data/native-certificate.json')
assert native['status']=='PASS_COMPLETE_NATIVE_RUP_REPLAY'
assert (native['core_clauses'],native['lemmas'],native['hints'])==(683,13299,554859)
pins(native['source_files_sha256']);pins(native['preserved_files_sha256'],H/'work/certificate')
core=read(H/'data/endpoint-core-review.json')
assert core['status']=='PASS_ORIGINAL_CORE_NATIVE_REPLAY_AND_GEOMETRY_REVIEW'
assert core['pair_occurrences']==42 and core['pair_unique_vertices']==37
assert not core['positive_parity_clauses_used'] and not core['endpoint_budget_counter_used']
pins(core['source_files_sha256'])
export=read(H/'data/endpoint-export-review.json');assert export['status'].startswith('PASS')
pins(export['source_files_sha256'])
plan=read(H/'data/proof-plan.json');pins(plan['source_files_sha256'])
assert plan['stats']['simulated'] and plan['stats']['slots']==1119
assert len(plan['module_order'])==51 and not plan['parity_clauses_present']
for x in plan['artifacts']:assert sha(H/x['path'])==x['sha256'],x['path']
progress=read(H/'data/replay-progress.json')
assert progress['status']=='PASS_COMPLETE_CNF_REFUTATION'
assert len(progress['checked_modules'])==progress['total_modules']==51
assert [x['module'] for x in progress['checked_modules']]==progress['ordered_modules']
assert set(progress['ordered_modules'])==set(plan['module_order'])
assert not (H/'data/replay.lock').exists()
reports=[]
for row in progress['checked_modules']:
 m=row['module'];rp=H/'data'/(m+'-audit.json');q=read(rp)
 assert sha(rp)==row['receipt_sha256']
 assert q['status']=='PASS_ENDPOINT_REPLAY_MODULE' and q['exit_code']==0 and not q['timeout']
 source=H/'lean'/(m.replace('.','/')+'.lean');obj=H/'build-replay'/(m.replace('.','/')+'.olean')
 assert sha(source)==q['source_sha256'] and sha(obj)==q['olean_sha256']
 assert sha(H/q['source_snapshot'])==q['source_sha256'] and sha(H/q['log'])==q['log_sha256']
 pins(q['dependencies'])
 assert not re.search(r'\b(sorry|admit|native_decide|axiom)\b',source.read_text(encoding='utf-8'))
 reports.extend(q['theorem_audits'])
for m,count in [('ActualCounters132',3),('CoreSemantics132',5),('ActualEndpoint132',2),('CreditLimitation132',2)]:
 rp=H/'data'/('independent-credit-audit.json' if m=='CreditLimitation132' else m+'-audit.json');q=read(rp)
 assert q['status']=='PASS' and q['exit_code']==0 and not q.get('timeout',False)
 assert len(q['axioms'])==count
 source=H/'lean'/(m+'.lean');assert sha(source)==q['source_sha256']
 for key in ['object','importable_object','log']:assert sha(q[key])==q[key+'_sha256']
 assert sha(Path(q['log']).parent/'source.lean.txt')==q['source_sha256']
 pins(q['dependencies']);reports.extend(q['axioms'])
 assert not re.search(r'\b(sorry|admit|native_decide|axiom)\b',source.read_text(encoding='utf-8'))
for row in reports:assert set(row['axioms'])<=allowed,row
assert any(x['theorem']=='Snake9.LocalWindow.Endpoint132.unsat' for x in reports)
assert any(x['theorem']=='Snake9.ActualEndpoint132.actual_pair_endpoint' for x in reports)
credit=read(H/'data/credit-limitation.json');assert credit['status']=='PASS_TWO_CYCLES_AND_UNIFORM_CREDIT_LIMITATION'
pins(credit['source_files_sha256'])
repair=read(H/'data/semantic-repair2.json');pins(repair['source_files_sha256'])
manifest=H/'data/file-manifest.json'
if not manifest.exists():
 assert len(sys.argv)==1
 paper=R/'paper/snake9_research.tex';editor=Path('D:/Codex/2026-10-13/new-chat/outputs/snake9_research.tex')
 assert sha(paper)==sha(editor)=='4667daec19f0b83af9fb129a263c8ae992757105414bad817c1ad13e1e11bb90'
 verification=dict(status='PASS_ACTUAL_PARITY_FREE_ENDPOINT_THEOREM',recorded_at=datetime.datetime.now(datetime.timezone.utc).isoformat(),
  complete_refutation_modules=51,core_clauses=683,derived_clauses=13299,propagation_hints=554859,
  actual_counter_theorems=3,actual_clause_theorems=5,actual_endpoint_theorems=2,
  conditional_arithmetic_theorems=2,all_axiom_reports=len(reports),allowed_axioms=sorted(allowed),
  new_unconditional_local_theorem=True,new_global_bound=False,parity_assumption=False,
  endpoint_quantifier='One actual endpoint has distance two from both centres.',
  final_audit_sha256=sha(H/'data/ActualEndpoint132-audit.json'),
  core_review_sha256=sha(H/'data/endpoint-core-review.json'),export_review_sha256=sha(H/'data/endpoint-export-review.json'),
  initial_semantic_failures_preserved=2,uniform_credit_limit='Conditional comparison remains above235 for allowance>=2.',
  sharp_gap_37_over_32853='Written and independently reviewed; current Lean statement checks strict inequality only.')
 (H/'data/verification.json').write_text(json.dumps(verification,indent=2)+'\n',encoding='utf-8')
 checkpoint=dict(status=verification['status'],goal_status='ACTIVE',previous_goal_turn='PROGRESS',
  base_commit='6002df5a28ac8154c5e1fbbbab982cb63a55da2a',
  prior_checkpoint_sha256=sha(R/'milestones/131-odd-pair-six-count/data/checkpoint.json'),
  verification_sha256=sha(H/'data/verification.json'),batch_observation_sha256=sha(H/'data/batch-observation.json'),
  current_interval=[191,235],interval_scope='Maintained contributor result with incomplete independent upper-proof rebuild.',
  paper_revision=126,next_paper_revision=136,paper_sha256=sha(paper),
  selected_next_task='Prove a sound restriction on occurrence and overlap of low-pair windows near actual endpoints.')
 (H/'data/checkpoint.json').write_text(json.dumps(checkpoint,indent=2)+'\n',encoding='utf-8')
 selected={p for p in H.rglob('*') if p.is_file() and p!=manifest and '__pycache__' not in p.parts
  and p.suffix not in ['.tmp','.lock'] and p.name!='stage-paths.nul'}
 selected.update(R/n for n in ['README.md','COLLABORATION.md','RESEARCH_LEDGER.md','WORKSPACE.md',
  'milestones/README.md','handoff/README.md','handoff/CURRENT_STATUS.md','handoff/NEXT_AGENT_PROMPT.md'])
 rows=[dict(path=p.relative_to(R).as_posix(),bytes=p.stat().st_size,sha256=sha(p)) for p in sorted(selected)]
 assert all(x['bytes']<100000000 for x in rows)
 manifest.write_text(json.dumps(dict(status='SAVED_COMPLETE_ENDPOINT_THEOREM132',files=rows,
  excluded_live_outputs='Other milestones remain live locally; frozen observations are included.'),indent=2)+'\n',encoding='utf-8')
j=read(manifest)
for x in j['files']:
 p=R/x['path'];assert p.stat().st_size==x['bytes'] and sha(p)==x['sha256'],x['path']
names={x['path'] for x in j['files']}|{manifest.relative_to(R).as_posix()}
g=['git','-c','core.commitGraph=false','-c','maintenance.auto=false','-c','gc.auto=0']
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
  if not n.startswith('milestones/132-odd-pair-endpoint/'):expected=expected.replace(b'\r\n',b'\n')
  assert b==expected,n
 proc.stdin.close();assert proc.wait()==0
print(json.dumps(dict(status='PASS_STAGED' if '--staged' in sys.argv else 'PASS_SAVED',files=len(names),
 bytes=sum(x['bytes'] for x in j['files'])+manifest.stat().st_size,new_unconditional_local_theorem=True,new_global_bound=False)))
