"""Verify evidence and freeze the checkpoint without treating partial traces as proofs."""
from pathlib import Path
import gzip,hashlib,json,re,subprocess,sys
H=Path(__file__).resolve().parents[1];R=H.parents[1]
read=lambda p:json.loads(p.read_text(encoding='utf-8-sig'))
cache={}
def digest(f):
 h=hashlib.sha256();size=0
 for b in iter(lambda:f.read(1024*1024),b''):h.update(b);size+=len(b)
 return h.hexdigest(),size
def sha(p):
 p=Path(p)
 if p not in cache:
  with p.open('rb') as f:cache[p]=digest(f)[0]
 return cache[p]
def pins(j,root=R):
 for name,d in j.items():
  p=Path(name);assert sha(p if p.is_absolute() else root/p)==d,name
archives=[read(H/'data'/('archive-'+n+'.json')) for n in ['augmented','reduced']]
for row in archives:
 arc=H/row['archive'];raw=H/row['original']
 assert sha(arc)==row['archive_sha256'] and arc.stat().st_size==row['archive_bytes']
 with gzip.open(arc,'rb') as f:assert digest(f)==(row['original_sha256'],row['original_bytes'])
 if raw.exists():assert sha(raw)==row['original_sha256'] and raw.stat().st_size==row['original_bytes']
 elif '--restore-archives' in sys.argv:
  with gzip.open(arc,'rb') as src,raw.open('xb') as out:
   for b in iter(lambda:src.read(1024*1024),b''):out.write(b)
  assert sha(raw)==row['original_sha256']
 assert sha(H/'scripts/archive_trace.py')==row['script_sha256']
p=read(H/'data/prelude.json');review=read(H/'data/prelude-review.json')
assert p['status']=='PASS_235_DIRECT_CLAUSES_DERIVED_FROM_ORIGINAL_CNF'
assert review['status']=='PASS_INDEPENDENT_ORIGINAL_ONLY_PRELUDE_REPLAY'
assert p['derived_clauses']==review['derived_clauses']==235 and p['total_hints']==review['total_hints']==132921
assert review['total_unit_propagations']==132686 and review['final_conflicts']==235
assert review['future_or_self_hints']==review['earlier_derived_hints']==0
assert review['all_hints_checked_in_order'] and review['hints_reference_only_original_inputs']
pins(p['source_pins']);pins(review['source_files_sha256'])
assert sha(H/'scripts/prepare.py')==p['script_sha256']
for file,key in [('work/original.cnf','original_sha256'),('work/augmented.cnf','augmented_sha256'),('work/prelude.lrat','prelude_sha256'),('data/direct-clauses.json','data_sha256')]:assert sha(H/file)==p[key]
red=read(H/'data/reduced.json');assert red['reduced_clauses']==101666 and red['occurring_variables']==4820
assert len(red['removed_clauses'])==4917 and len(red['removed_auxiliary_variables'])==2457
assert sha(H/'scripts/prepare_reduced.py')==red['script_sha256'] and sha(H/'work/reduced.cnf')==red['reduced_sha256']
a=read(H/'data/search-audit.json');pins(a['pins'],H)
assert sha(H/'scripts/audit_search.py')==a['script_sha256']
assert len(a['attempts'])==2 and all(x['status']=='TIMEOUT' and x['initial_native_deductions_replayed']==1000 and not x['final_empty_clause_verified'] and not x['full_native_proof_replayed'] for x in a['attempts'])
for name,script in [('search.json','search.py'),('search-reduced.json','search_reduced.py')]:
 j=read(H/'data'/name);assert j['status']=='TIMEOUT' and j['exit_code'] not in [10,20]
 assert sha(H/'scripts'/script)==j['script_sha256']
 assert sha(Path(j['command'][0]))==j['solver_sha256']
receipt=H/'logs/direct-cardinality-1793686604453734400/record.json';q=read(receipt)
assert q['status']=='PASS' and q['exit_code']==0 and not q.get('timeout',False)
assert q['dependencies_unchanged'];pins(q['dependencies'])
source=H/'lean/DirectCardinality127.lean';checker=H/'audit/check_direct_cardinality.py'
assert sha(source)==q['source_sha256']==q['source_current_sha256']==sha(receipt.parent/'source.lean.txt')
assert sha(checker)==q['checker_sha256']==q['checker_current_sha256']==sha(receipt.parent/'checker.py.txt')
assert sha(Path(q['object']))==q['object_sha256'] and sha(Path(q['log']))==q['log_sha256']
assert len(q['axioms'])==5 and all(set(x['axioms'])<={'propext','Classical.choice','Quot.sound'} for x in q['axioms'])
assert not re.search(r'\b(sorry|admit|native_decide|axiom)\b',source.read_text(encoding='utf-8'))
task=read(H/'data/next-pair-task.json');pins(task['source_pins'])
assert task['status']=='PROPOSED_NOT_ENCODED_OR_SEARCHED' and task['pair_corner_occurrences']==42 and task['pair_distinct_corners']==37 and task['selected_sum_upper']==34
obs=read(H/'data/batch-observation.json')
for row in obs['batches']:
 assert row['pid']==row['process']['ProcessId'] and row['batch'] in row['process']['CommandLine']
 assert sha(H/row['snapshot'])==row['sha256']
 if 'checker_snapshot' in row:assert sha(H/row['checker_snapshot'])==row['checker_snapshot_sha256']
paper=R/'paper/snake9_research.tex';editor=Path('D:/Codex/2026-10-13/new-chat/outputs/snake9_research.tex')
assert sha(paper)==sha(editor)=='4667daec19f0b83af9fb129a263c8ae992757105414bad817c1ad13e1e11bb90'
manifest=H/'data/file-manifest.json'
if '--verify' not in sys.argv and '--staged' not in sys.argv and '--restore-archives' not in sys.argv:
 assert not manifest.exists() and not (H/'data/verification.json').exists()
 names=['data/prelude.json','data/prelude-review.json','data/reduced.json','data/search-audit.json','data/next-pair-task.json','audit/prelude-review.md','audit/reduced-encoding-review.md','audit/direct-cardinality-derivation.md','MATHEMATICAL_NOTE.md','data/batch-observation.json']
 v=dict(status='PASS_DIRECT_CLAUSE_CHECKPOINT_NO_NEW_COUNT_FLOOR',pins={n:sha(H/n) for n in names},lean_receipt=receipt.relative_to(H).as_posix(),lean_receipt_sha256=sha(receipt),lean_modules=1,axiom_reports=5,direct_clauses=235,ordered_references=132921,original_formula_independently_rebuilt=True,new_definitions=0,new_count_floor=False,new_global_bound=False,native_attempts=a['attempts'],archives=archives,next_pair_counter_implemented=False,scope='Generic Lean cardinality proofs; independently reconstructed original formula and all235 original-input RUP derivations; smaller input and bounded trace-ID checks. Two native timeouts, no complete contradiction or improved bound.')
 (H/'data/verification.json').write_text(json.dumps(v,indent=2)+'\n',encoding='utf-8')
 prior=R/'milestones/126-paper-revision/data/checkpoint.json'
 c=dict(status=v['status'],base_commit='c57e9e87606cc879bfe860ad3af79c3e25276f0a',previous_goal_turn='PROGRESS',goal_status='ACTIVE',verification_sha256=sha(H/'data/verification.json'),prior_checkpoint=prior.relative_to(R).as_posix(),prior_checkpoint_sha256=sha(prior),paper_revision=126,next_paper_revision=136,paper_sha256=sha(paper),current_interval=[191,235],interval_scope='Maintained prior result with documented upper-proof rebuild limitation.',batches=obs['batches'])
 (H/'data/checkpoint.json').write_text(json.dumps(c,indent=2)+'\n',encoding='utf-8')
 raw={H/x['original'] for x in archives}
 files=[p for p in H.rglob('*') if p.is_file() and p!=manifest and p not in raw and '__pycache__' not in p.parts]
 files += [R/n for n in ['README.md','COLLABORATION.md','RESEARCH_LEDGER.md','WORKSPACE.md','milestones/README.md','handoff/README.md','handoff/CURRENT_STATUS.md','handoff/NEXT_AGENT_PROMPT.md']]
 rows=[dict(path=p.relative_to(R).as_posix(),bytes=p.stat().st_size,sha256=sha(p)) for p in sorted(set(files))]
 assert all(x['bytes']<100000000 for x in rows)
 manifest.write_text(json.dumps(dict(status='SAVED_DIRECT_CARDINALITY127',files=rows,excluded_redundant_raw_traces=archives),indent=2)+'\n',encoding='utf-8')
j=read(manifest)
for row in j['files']:
 f=R/row['path'];assert f.stat().st_size==row['bytes'] and sha(f)==row['sha256'],row['path']
if '--staged' in sys.argv:
 names={x['path'] for x in j['files']}|{manifest.relative_to(R).as_posix()};g=['git','-c','core.commitGraph=false']
 actual=set(subprocess.check_output(g+['diff','--cached','--name-only','-z'],cwd=R).decode().strip('\0').split('\0'))
 assert actual==names,(actual-names,names-actual)
 for name in names:
  saved=(R/name).read_bytes();expected=saved if name.startswith('milestones/127-direct-cardinality/') else saved.replace(b'\r\n',b'\n')
  assert subprocess.check_output(g+['show',':'+name],cwd=R)==expected,name
print(json.dumps(dict(status='PASS_STAGED' if '--staged' in sys.argv else 'PASS_SAVED',files=len(j['files'])+1,bytes=sum(x['bytes'] for x in j['files'])+manifest.stat().st_size,lean_modules=1,axiom_reports=5,native_outcomes=['TIMEOUT','TIMEOUT'],new_count_floor=False,new_global_bound=False,paper_unchanged=True,goal='ACTIVE'),indent=2))
