"""Verify and freeze this checkpoint; preserve the boundary between semantics and refutation."""
from pathlib import Path
import gzip,hashlib,json,re,subprocess,sys
H=Path(__file__).resolve().parents[1];R=H.parents[1]
read=lambda p:json.loads(p.read_text(encoding='utf-8-sig'))
cache={}
def digest(f):
 h=hashlib.sha256();n=0
 for b in iter(lambda:f.read(1024*1024),b''):h.update(b);n+=len(b)
 return h.hexdigest(),n
def sha(p):
 p=Path(p)
 if p not in cache:
  with p.open('rb') as f:cache[p]=digest(f)[0]
 return cache[p]
def pins(rows,root=R):
 for name,d in rows.items():
  p=Path(name);assert sha(p if p.is_absolute() else root/p)==d,name
prep=read(H/'data/preparation.json');pins(prep['source_pins'])
assert (prep['clauses'],prep['occurring_variables'],prep['new_counter_clauses'])==(104529,6248,2863)
assert sha(H/'scripts/prepare.py')==prep['script_sha256']
assert sha(H/'work/pair.cnf')==prep['cnf_sha256']
assert sha(H/'data/pair-counter.json')==prep['counter_sha256']
review=read(H/'data/pair-review.json');pins(review['source_files_sha256'])
assert review['status']=='PASS_INDEPENDENT_PAIR_COUNTER_INPUT_AUDIT'
assert review['exact_new_counter_serialization'] and review['fresh_variables_disjoint']
assert review['native_prefix']['deductions']==1000 and review['native_prefix']['ordered_hints']==2643
assert not review['native_prefix']['empty_clause_in_checked_prefix']
lean_data=read(H/'data/lean-data-review.json');pins(lean_data['pins'],H)
assert lean_data['status']=='PASS_EXACT_LEAN_PAIR_DATA_AND_CNF_TAIL'
assert (lean_data['clauses'],lean_data['tags'],lean_data['meanings_checked'])==(2863,2863,8706)
search=read(H/'data/search.json')
assert search['status']=='TIMEOUT' and search['exit_code'] not in [10,20]
assert sha(H/'scripts/search.py')==search['script_sha256']
assert sha(Path(search['command'][0]))==search['solver_sha256']
arc=read(H/'data/archive-pair.json');archive=H/arc['archive'];raw=H/arc['original']
assert sha(archive)==arc['archive_sha256'] and archive.stat().st_size==arc['archive_bytes']
with gzip.open(archive,'rb') as f:assert digest(f)==(arc['original_sha256'],arc['original_bytes'])
assert arc['original_sha256']==search['raw_sha256'] and arc['original_bytes']==search['raw_bytes']
assert sha(H/'scripts/archive_trace.py')==arc['script_sha256']
if raw.exists():assert sha(raw)==arc['original_sha256']
elif '--restore-archives' in sys.argv:
 with gzip.open(archive,'rb') as src,raw.open('xb') as out:
  for b in iter(lambda:src.read(1024*1024),b''):out.write(b)
 assert sha(raw)==arc['original_sha256']
receipts=[]
for module,checker,expected in [('PairLower128','check_pair_lower.py',6),('PairClauses128','check_pair_clauses.py',4)]:
 candidates=[]
 for p in (H/'logs').glob('*/record.json'):
  q=read(p)
  if q['status']=='PASS' and Path(q.get('importable_object','')).stem==module:candidates.append((p,q))
 assert len(candidates)==1,(module,len(candidates))
 p,q=candidates[0];src=H/'lean'/(module+'.lean');check=H/'audit'/checker
 assert q['exit_code']==0 and not q.get('timeout') and q['dependencies_unchanged']
 pins(q['dependencies'])
 assert sha(src)==q['source_sha256']==q['source_current_sha256']==sha(p.parent/'source.lean.txt')
 assert sha(check)==q['checker_sha256']==q['checker_current_sha256']==sha(p.parent/'checker.py.txt')
 for field in ['object','importable_object','log']:assert sha(Path(q[field]))==q[field+'_sha256']
 assert len(q['axioms'])==expected and all(set(x['axioms'])<={'propext','Classical.choice','Quot.sound'} for x in q['axioms'])
 assert not re.search(r'\b(sorry|admit|native_decide|axiom)\b',src.read_text(encoding='utf-8'))
 receipts.append(dict(module=module,path=p.relative_to(H).as_posix(),sha256=sha(p),axiom_reports=expected,seconds=q['seconds']))
task=read(H/'data/next-case-task.json');pins(task['source_pins'])
assert task['status']=='PROPOSED_EXHAUSTIVE_SPLIT_NOT_ENCODED_OR_SEARCHED'
assert sha(H/'scripts/write_next_task.py')==task['script_sha256']
split=read(H/'data/next-split-counts.json')
assert split['status']=='PASS_EXHAUSTIVE_INTEGER_VECTOR_SPLIT_ONLY'
assert sha(H/'audit/count_next_split.py')==split['script_sha256']
assert (split['fourth_equals_three'],split['fourth_at_least_four'])==(1287,14014)
obs=read(H/'data/batch-observation.json')
assert sha(H/'scripts/observe_batches.py')==obs['script_sha256']
for row in obs['batches']:
 assert row['pid']==row['process']['ProcessId'] and row['batch'] in row['process']['CommandLine']
 assert sha(H/row['snapshot'])==row['sha256']
 if 'checker_snapshot' in row:assert sha(H/row['checker_snapshot'])==row['checker_snapshot_sha256']
paper=R/'paper/snake9_research.tex';editor=Path('D:/Codex/2026-10-13/new-chat/outputs/snake9_research.tex')
assert sha(paper)==sha(editor)=='4667daec19f0b83af9fb129a263c8ae992757105414bad817c1ad13e1e11bb90'
manifest=H/'data/file-manifest.json'
if not any(x in sys.argv for x in ['--verify','--staged','--restore-archives']):
 assert not manifest.exists() and not (H/'data/verification.json').exists()
 names=['data/preparation.json','data/pair-review.json','data/lean-data-review.json','data/search.json','data/next-case-task.json','data/next-split-counts.json',
        'audit/pair-counter-review.md','audit/pair-derivation.md','MATHEMATICAL_NOTE.md','data/batch-observation.json']
 v=dict(status='PASS_PAIR_COUNTER_SEMANTICS_NO_NEW_COUNT_FLOOR',pins={n:sha(H/n) for n in names},
  lean_receipts=receipts,lean_modules=2,axiom_reports=10,new_count_floor=False,new_global_bound=False,
  added_clauses=2863,complete_combined_input_semantics=False,complete_refutation=False,
  original_only_derivation=False,native_status='TIMEOUT',native_prefix_deductions=1000,
  archive=arc,scope='Lean checks actual selected-occurrence cap34 and satisfaction of all added2863 clauses. The complete104529-clause conjunction and a final contradiction remain unchecked. No new six-count floor or global bound.')
 (H/'data/verification.json').write_text(json.dumps(v,indent=2)+'\n',encoding='utf-8')
 prior=R/'milestones/127-direct-cardinality/data/checkpoint.json'
 c=dict(status=v['status'],base_commit='7573dd064f9245ca2210f00a70679f97dc3792e6',previous_goal_turn='PROGRESS',goal_status='ACTIVE',
  verification_sha256=sha(H/'data/verification.json'),prior_checkpoint=prior.relative_to(R).as_posix(),prior_checkpoint_sha256=sha(prior),
  paper_revision=126,next_paper_revision=136,paper_sha256=sha(paper),current_interval=[191,235],
  interval_scope='Maintained prior result with documented independent upper-proof rebuild limitation.',batches=obs['batches'])
 (H/'data/checkpoint.json').write_text(json.dumps(c,indent=2)+'\n',encoding='utf-8')
 files=[p for p in H.rglob('*') if p.is_file() and p not in [manifest,raw] and '__pycache__' not in p.parts]
 files += [R/n for n in ['README.md','COLLABORATION.md','RESEARCH_LEDGER.md','WORKSPACE.md','milestones/README.md','handoff/README.md','handoff/CURRENT_STATUS.md','handoff/NEXT_AGENT_PROMPT.md']]
 rows=[dict(path=p.relative_to(R).as_posix(),bytes=p.stat().st_size,sha256=sha(p)) for p in sorted(set(files))]
 assert all(x['bytes']<100000000 for x in rows)
 manifest.write_text(json.dumps(dict(status='SAVED_PAIR_COUNTER128',files=rows,excluded_redundant_raw_trace=arc),indent=2)+'\n',encoding='utf-8')
j=read(manifest)
for row in j['files']:
 p=R/row['path'];assert p.stat().st_size==row['bytes'] and sha(p)==row['sha256'],row['path']
if '--staged' in sys.argv:
 names={x['path'] for x in j['files']}|{manifest.relative_to(R).as_posix()};g=['git','-c','core.commitGraph=false']
 actual=set(subprocess.check_output(g+['diff','--cached','--name-only','-z'],cwd=R).decode().strip('\0').split('\0'))
 assert names==actual,(actual-names,names-actual)
 for name in names:
  saved=(R/name).read_bytes();expected=saved if name.startswith('milestones/128-coupled-pair/') else saved.replace(b'\r\n',b'\n')
  assert subprocess.check_output(g+['show',':'+name],cwd=R)==expected,name
print(json.dumps(dict(status='PASS_STAGED' if '--staged' in sys.argv else 'PASS_SAVED',files=len(j['files'])+1,
 bytes=sum(x['bytes'] for x in j['files'])+manifest.stat().st_size,lean_modules=2,axiom_reports=10,
 native_outcome='TIMEOUT',new_count_floor=False,new_global_bound=False,paper_unchanged=True,goal='ACTIVE'),indent=2))
