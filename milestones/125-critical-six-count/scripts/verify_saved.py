"""Verify the reviewed checkpoint, including lossless archives of partial traces."""
from pathlib import Path
import gzip,hashlib,json,subprocess,sys
H=Path(__file__).resolve().parents[1];R=H.parents[1]
read=lambda p:json.loads(p.read_text(encoding='utf-8-sig'))
cache={}
def digest(stream):
 h=hashlib.sha256();size=0
 for b in iter(lambda:stream.read(1024*1024),b''):h.update(b);size+=len(b)
 return h.hexdigest(),size
archive_rows=[read(H/'data/partial-proof-archive.json')]+read(H/'data/partial-proof-archives-extra.json')['archives']
archives={(H/x['original']).resolve():H/x['archive'] for x in archive_rows}
def sha(p):
 p=Path(p).resolve()
 if p not in cache:
  if p.exists():
   with p.open('rb') as f:cache[p]=digest(f)[0]
  else:
   assert p in archives,('Missing file',str(p))
   with gzip.open(archives[p],'rb') as f:cache[p]=digest(f)[0]
 return cache[p]
def pins(j):
 for p,d in j.items():
  q=Path(p);assert sha(q if q.is_absolute() else R/q)==d,p
for x in archive_rows:
 assert sha(H/x['archive'])==x['archive_sha256']
 assert (H/x['archive']).stat().st_size==x['archive_bytes']
 with gzip.open(H/x['archive'],'rb') as f:assert digest(f)==(x['original_sha256'],x['original_bytes'])
 assert sha(H/x['original'])==x['original_sha256']
assert sha(H/'scripts/archive_partial.py')==read(H/'data/partial-proof-archive.json')['script_sha256']
assert sha(H/'scripts/archive_remaining.py')==read(H/'data/partial-proof-archives-extra.json')['script_sha256']

review=read(H/'data/proof-review.json');supplement=read(H/'data/proof-supplement.json')
assert review['status']=='PASS_STRUCTURAL125_RECEIPT_AND_MATHEMATICAL_SCOPE'
assert supplement['status']=='PASS_EMPTY_TRADEOFF_AND_ACTUAL_INTERVAL_SUPPLEMENT'
assert (review['reviewed_modules'],review['axiom_reports'])==(1,12)
assert (supplement['reviewed_modules'],supplement['axiom_reports'])==(2,7)
for j,script in [(review,'audit_receipts.py'),(supplement,'audit_supplement.py')]:
 pins(j['verified_file_hashes']);pins(j['additional_pins'])
 assert sha(H/'scripts'/script)==j['script_sha256']
for name,reports in [('Structural125',12),('EmptyTradeoff125',2),('ActualBounds125',5)]:
 j=read(H/'data'/(name+'-audit.json'))
 assert j['exit_code']==0 and not j['timeout'] and j['status']=='PASS_REFERENCE_RECOVERY_MODULE'
 assert len(j['theorem_audits'])==reports
 assert all(set(a['axioms'])<={'propext','Classical.choice','Quot.sound'} for a in j['theorem_audits'])
 assert sha(H/'lean'/(name+'.lean'))==j['source_sha256']
 assert sha(H/'build-isolated'/(name+'.olean'))==j['olean_sha256']
search=read(H/'data/search-audit.json');bounded=read(H/'data/bounded-search-audit.json')
for j,script in [(search,'audit_search.py'),(bounded,'audit_bounded_search.py')]:
 pins(j['source_files_sha256']);assert sha(H/'scripts'/script)==j['script_sha256']
attempts=search['attempts']+bounded['attempts'];assert len(attempts)==3
assert all(a['solver_status']=='TIMEOUT' and not a['raw_proof_complete'] for a in attempts)
assert all(a['full_formula_rebuilt'] and a['all_cut_cycles_verified'] for a in attempts)
assert [(a['variables'],a['clauses']) for a in attempts]==[(5072,101933),(4820,101431),(7277,106348)]
task=read(H/'data/next-encoding-task.json');assert task['status']=='PROPOSED_NOT_IMPLEMENTED'
assert task['original_clauses']==106348 and task['direct_clauses']==235
for p,d in task['source_pins'].items():assert sha(H/p)==d,p
obs=read(H/'data/batch-observation.json');assert len(obs['batches'])==3
for b in obs['batches']:
 assert sha(H/b['snapshot'])==b['sha256']
 assert b['pid']==b['process']['ProcessId'] and b['batch'] in b['process']['CommandLine']
 if 'checker_snapshot' in b:assert sha(H/b['checker_snapshot'])==b['checker_snapshot_sha256']
paper=R/'paper/snake9_research.tex';editor=Path('D:/Codex/2026-10-13/new-chat/outputs/snake9_research.tex')
assert sha(paper)==sha(editor)=='5e62b785321b8b624338e484560f3ac16d048699c841deeccc69573fd13be72f'
manifest=H/'data/file-manifest.json';status='PASS_RETAINED_EMPTY_SQUARE_CRITERIA_AND_ACTUAL_INTERVALS'
if '--verify' not in sys.argv and '--staged' not in sys.argv:
 assert not manifest.exists() and not (H/'data/check.lock').exists()
 assert not (H/'data/verification.json').exists() and not (H/'data/checkpoint.json').exists()
 names=['MATHEMATICAL_NOTE.md','data/proof-review.json','audit/proof-review.md','data/proof-supplement.json','audit/proof-supplement.md',
  'data/search-audit.json','audit/search-review.md','data/bounded-search-audit.json','audit/bounded-search-review.md',
  'audit/structural-derivation.md','data/next-encoding-task.json','data/partial-proof-archive.json',
  'data/partial-proof-archives-extra.json','data/batch-observation.json']
 v=dict(status=status,pins={p:sha(H/p) for p in names},reviewed_modules=3,axiom_reports=19,
  previous_goal_turn='PROGRESS',new_unconditional_count_floor=False,new_global_upper_bound=False,
  actual_window_restriction_checked=True,retained_empty_square_criterion_checked=True,
  native_attempts=[dict(name=a['name'],status=a['solver_status'],seconds=a['seconds']) for a in attempts],
  next_encoding_implemented=False,
  scope='Checked actual-snake necessary interval restrictions and retained-empty-square conditional length criteria. Three searches timed out. No new local count floor or unconditional global length bound.')
 (H/'data/verification.json').write_text(json.dumps(v,indent=2)+'\n')
 prior=R/'milestones/124-six-count-cycle-pressure/data/checkpoint.json'
 c=dict(status=status,verification_sha256=sha(H/'data/verification.json'),prior_checkpoint=prior.relative_to(R).as_posix(),
  prior_checkpoint_sha256=sha(prior),base_commit='11cb3beae2347ac80f04b9da08324d43ed9ee271',goal_status='ACTIVE',
  current_interval=[191,235],interval_scope='Maintained prior result with documented independent rebuild limitation; no new unconditional bound.',
  paper_revision=116,next_paper_revision=126,paper_sha256=sha(paper),batches=obs['batches'])
 (H/'data/checkpoint.json').write_text(json.dumps(c,indent=2)+'\n')
 selected=[p for p in H.rglob('*') if p.is_file() and p!=manifest and p.resolve() not in archives and '__pycache__' not in p.parts and p.suffix!='.lock']
 selected += [R/p for p in ['README.md','COLLABORATION.md','RESEARCH_LEDGER.md','milestones/README.md','handoff/README.md','handoff/CURRENT_STATUS.md','handoff/NEXT_AGENT_PROMPT.md']]
 rows=[dict(path=p.relative_to(R).as_posix(),bytes=p.stat().st_size,sha256=sha(p)) for p in sorted(set(selected))]
 assert all(x['bytes']<100000000 for x in rows)
 manifest.write_text(json.dumps(dict(status='SAVED_IMMUTABLE_SIX_COUNT_RESEARCH125',files=rows,excluded_raw_traces=archive_rows,
  scope='All milestone125 files except three redundant uncompressed traces, preserved through verified gzip archives and locally retained originals, plus seven handover documents. Old live proof batches remain separate.'),indent=2)+'\n')
 print('SAVED_MANIFEST',len(rows),sum(x['bytes'] for x in rows),'bytes')
else:
 v=read(H/'data/verification.json');c=read(H/'data/checkpoint.json')
 assert c['status']==v['status']==status and sha(H/'data/verification.json')==c['verification_sha256']
 assert sha(R/c['prior_checkpoint'])==c['prior_checkpoint_sha256']
 for p,d in v['pins'].items():assert sha(H/p)==d,p
 rows=read(manifest)['files']
 for x in rows:
  p=R/x['path'];assert p.stat().st_size==x['bytes'] and sha(p)==x['sha256'],x['path']
 if '--staged' in sys.argv:
  files=[x['path'] for x in rows]+[manifest.relative_to(R).as_posix()]
  actual=subprocess.check_output(['git','-c','core.commitGraph=false','diff','--cached','--name-only'],cwd=R,text=True).splitlines()
  assert set(actual)==set(files),'Index differs from reviewed snapshot'
  output=''.join(subprocess.check_output(['git','-c','core.commitGraph=false','ls-files','-s','--',*files[i:i+50]],cwd=R,text=True) for i in range(0,len(files),50))
  blobs={line.split('\t',1)[1]:line.split()[1] for line in output.splitlines()}
  for name in files:
   raw=(R/name).read_bytes()
   if not name.startswith('milestones/125-'):raw=raw.replace(b'\r\n',b'\n')
   assert hashlib.sha1(b'blob '+str(len(raw)).encode()+b'\0'+raw).hexdigest()==blobs[name],name
 print('PASS_EXACT_STAGED_FILES' if '--staged' in sys.argv else 'PASS_LOCAL_MANIFEST',len(rows))
