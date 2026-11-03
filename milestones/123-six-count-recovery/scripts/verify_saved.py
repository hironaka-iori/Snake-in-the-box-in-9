"""Save and verify the exact reviewed checkpoint; old live batches stay separate."""
from pathlib import Path
import datetime,hashlib,json,subprocess,sys
H=Path(__file__).resolve().parents[1];R=H.parents[1]
read=lambda p:json.loads(p.read_text(encoding='utf-8-sig'))
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
review=read(H/'data/proof-review.json')
assert review['reviewed_modules']==5 and review['axiom_reports']==7
for p,d in {**review['verified_file_hashes'],**review['additional_pins']}.items():
 q=Path(p);assert sha(q if q.is_absolute() else R/q)==d,p
assert sha(H/'scripts/audit_receipts.py')==review['script_sha256']
case=read(H/'data/case10-plan.json')
assert len(case['modules'])==202
for row in case['ports']:
 assert sha(H/row['original'])==row['sha256']
 assert sha(H/row['isolated'])==row['isolated_sha256']
assert sha(H/'scripts/export_case10.py')==case['script_sha256']
assert sha(H/'data/case10-recovery.json')==case['recovery_sha256']
for name in ['CaseSemantics123','SixCharge123','GuardedCharge123']:
 a=read(H/'data'/(name+'-audit.json'));assert a['exit_code']==0 and not a['timeout']
 assert all(set(x['axioms'])<={'propext','Classical.choice','Quot.sound'} for x in a['theorem_audits'])
probe=read(H/'data/probes/0123042-total25-resume.json')
assert probe['status']=='UNSAT_UNCERTIFIED' and probe['selected'] is None and probe['cap']==25
assert len(probe['cycle_cuts'])==19 and probe['initial_cycle_cuts']==13
bank=read(H/'data/six-sum-bank.json')
assert (bank['paths'],bank['pairs_checked'],bank['case10_occurrences'],bank['case10_minimum']['total'])==(134,2432200,1298,43)
for p,d in bank['source_pins'].items():assert sha(R/p)==d,p
assert sha(H/'scripts/scan_six_sum.py')==bank['script_sha256']
results=[]
for p in sorted((H/'data').glob('*graph*/results.json')):
 j=read(p);assert all(x['all_edge_inequalities_checked'] for x in j['profiles'])
 for q,d in j['source_files_sha256'].items():assert sha(R/q)==d,q
 results.append(dict(path=p.relative_to(H).as_posix(),sha256=sha(p),profiles=[{k:x[k] for k in ['profile','mean','comparison_bound','comparison_integer_bound']} for x in j['profiles']]))
assert len(results)>=8
obs=read(H/'data/batch-observation.json')
for b in obs['batches']:
 assert sha(H/b['snapshot'])==b['sha256']
 assert b['pid']==b['process']['ProcessId'] and b['batch'] in b['process']['CommandLine']
 if 'checker_snapshot' in b:assert sha(H/b['checker_snapshot'])==b['checker_snapshot_sha256']
paper=R/'paper/snake9_research.tex';editor=Path('D:/Codex/2026-10-13/new-chat/outputs/snake9_research.tex')
assert sha(paper)==sha(editor)=='5e62b785321b8b624338e484560f3ac16d048699c841deeccc69573fd13be72f'
manifest=H/'data/file-manifest.json'
if '--verify' not in sys.argv and '--staged' not in sys.argv:
 assert not manifest.exists() and not (H/'data/check.lock').exists()
 names=['MATHEMATICAL_NOTE.md','data/proof-review.json','audit/proof-review.md','data/case10-audit.json','audit/case10-review.md','data/six-sum-probe-audit.json','audit/six-sum-probe-review.md','audit/six-graph-review.md','audit/six-sum-graph-review.md','audit/six-sum-guarded-review.md','data/batch-observation.json']
 pins={p:sha(H/p) for p in names}
 v=dict(status='PASS_SIX_COUNT_ACCOUNTING_AND_GRAPH_OBSTRUCTION',pins=pins,reviewed_modules=5,axiom_reports=7,graphs=results,
  candidate_floor=26,candidate_floor_proved=False,case10_refutation_checked=False,new_global_upper_bound=False,previous_goal_turn='PROGRESS',
  scope='Five checked semantic/accounting modules, saved original case10 recovery, audited native floor26 evidence and exact finite graph limitations. No new arbitrary-snake exclusion or global upper bound.')
 (H/'data/verification.json').write_text(json.dumps(v,indent=2)+'\n')
 prior=R/'milestones/122-endpoint-equality/data/checkpoint.json'
 c=dict(status=v['status'],verification_sha256=sha(H/'data/verification.json'),prior_checkpoint=prior.relative_to(R).as_posix(),prior_checkpoint_sha256=sha(prior),
  base_commit='1d0e6c673431bcc90ff374cd87af44560eece917',paper_revision=116,next_paper_revision=126,paper_sha256=sha(paper),goal_status='ACTIVE',
  current_interval=[191,235],interval_scope='Maintained prior result with documented independent rebuild limitation; conditional234 remains unresolved.',batches=obs['batches'])
 (H/'data/checkpoint.json').write_text(json.dumps(c,indent=2)+'\n')
 selected=[p for p in H.rglob('*') if p.is_file() and p!=manifest and '__pycache__' not in p.parts and p.suffix!='.lock']
 selected += [R/p for p in ['README.md','COLLABORATION.md','RESEARCH_LEDGER.md','milestones/README.md','handoff/README.md','handoff/CURRENT_STATUS.md','handoff/NEXT_AGENT_PROMPT.md']]
 rows=[dict(path=p.relative_to(R).as_posix(),bytes=p.stat().st_size,sha256=sha(p)) for p in sorted(set(selected))]
 assert all(x['bytes']<100000000 for x in rows)
 manifest.write_text(json.dumps(dict(status='SAVED_IMMUTABLE_SIX_COUNT_RESEARCH123',files=rows,scope='All saved milestone123 files and seven updated handover documents. Prior live proof batches remain separate.'),indent=2)+'\n')
 print('SAVED_MANIFEST',len(rows),sum(x['bytes'] for x in rows),'bytes')
else:
 v=read(H/'data/verification.json');c=read(H/'data/checkpoint.json')
 assert c['status']==v['status']=='PASS_SIX_COUNT_ACCOUNTING_AND_GRAPH_OBSTRUCTION'
 assert sha(H/'data/verification.json')==c['verification_sha256']
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
   if not name.startswith('milestones/123-'):raw=raw.replace(b'\r\n',b'\n')
   assert hashlib.sha1(b'blob '+str(len(raw)).encode()+b'\0'+raw).hexdigest()==blobs[name],name
 print('PASS_EXACT_STAGED_FILES' if '--staged' in sys.argv else 'PASS_LOCAL_MANIFEST',len(rows))
