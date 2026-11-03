"""Save and verify the exact reviewed checkpoint; old live batches stay separate."""
from pathlib import Path
import hashlib,json,subprocess,sys
H=Path(__file__).resolve().parents[1];R=H.parents[1]
read=lambda p:json.loads(p.read_text(encoding='utf-8-sig'))
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()

def verify_pins(pins):
 for p,d in pins.items():
  q=Path(p);assert sha(q if q.is_absolute() else R/q)==d,p

review=read(H/'data/proof-review.json')
assert review['status']=='PASS_ALL46_MODULES_SINGLE_SHAPE_AND_CONDITIONAL_ACTUAL_BOUNDS'
assert review['reviewed_modules']==46 and review['axiom_reports']==22
verify_pins(review['source_files_sha256'])
assert sha(H/'scripts/audit_receipts.py')==review['script_sha256']
plan=read(H/'data/total341-plan.json')
assert len(plan['modules'])==40 and len(plan['artifacts'])==83
expected=set(plan['modules'])|{'UniformSixBound124','TotalGeometry124','ActualTotal124','Reversal124','SixDeficit124','ActualUniform124'}
assert {r['module'] for r in review['modules']}==expected
assert len(review['modules'])==len(expected)==46
for row in review['modules']:
 r=read(R/row['receipt'])
 assert r['exit_code']==0 and not r['timeout']
 assert all(set(x['axioms'])<={'propext','Classical.choice','Quot.sound'} for x in r['theorem_audits'])
verify_pins(plan['input_pins'])
for row in plan['artifacts']:assert sha(H/row['path'])==row['sha256'],row['path']
assert sha(H/'scripts/export_sum.py')==plan['exporter_sha256']
assert len(review['preserved_export_attempts'])==2
assert all(x['status']=='STOPPED' for x in review['preserved_export_attempts'])

certificate=read(H/'data/certificate-audit.json')
assert certificate['status']=='PASS_EXACT_FORMULA_MULTIPLICITIES_CORE_RUP_AND_EXPORTED_DATA'
verify_pins(certificate['source_files_sha256'])
assert sha(H/'scripts/audit_certificate.py')==certificate['script_sha256']
probe=read(H/'data/probe-audit.json')
assert probe['status']=='PASS_SIX_COUNT_PROBES_AND_NATIVE_COVERAGE_AUDIT'
assert probe['probe_records']==29 and probe['current_probe_records']==28
assert probe['current_coverage_counts']=={'UNKNOWN':2,'NATIVE_NEGATIVE':19}
assert (probe['cut_records'],probe['unique_cut_vertex_sets'])==(120,81)
assert probe['universal_floor25_proved'] is False and probe['universal_floor26_proved'] is False
verify_pins(probe['source_pins'])
assert sha(H/'scripts/audit_probes.py')==probe['script_sha256']
for row in probe['probes']:assert sha(R/row['probe'])==row['probe_sha256']
coverage=read(H/'data/coverage-audit.json')
assert (coverage['restricted_growth_words'],coverage['induced_words'],coverage['reversal_classes'])==(877,34,21)
assert len(coverage['attaining_paths_rechecked'])==12 and coverage['attaining_path_pairs_checked']==220032
verify_pins(coverage['verified_file_hashes'])
assert sha(H/'scripts/audit_coverage.py')==coverage['script_sha256']

graph_path=H/'data/graph-26-25-25/results.json';graph=read(graph_path)
assert all(x['all_edge_inequalities_checked'] for x in graph['profiles'])
assert {x['profile']:x['comparison_integer_bound'] for x in graph['profiles']}=={'completed':235,'conditional_floor18':234}
verify_pins(graph['source_files_sha256'])
obs=read(H/'data/batch-observation.json')
assert len(obs['batches'])==3
for b in obs['batches']:
 assert sha(H/b['snapshot'])==b['sha256']
 assert b['pid']==b['process']['ProcessId'] and b['batch'] in b['process']['CommandLine']
 if 'checker_snapshot' in b:assert sha(H/b['checker_snapshot'])==b['checker_snapshot_sha256']
paper=R/'paper/snake9_research.tex';editor=Path('D:/Codex/2026-10-13/new-chat/outputs/snake9_research.tex')
assert sha(paper)==sha(editor)=='5e62b785321b8b624338e484560f3ac16d048699c841deeccc69573fd13be72f'
manifest=H/'data/file-manifest.json'
status='PASS_ONE_SIX_COUNT_CLASS_AND_CONDITIONAL_LENGTH_CRITERIA'
if '--verify' not in sys.argv and '--staged' not in sys.argv:
 assert not manifest.exists() and not (H/'data/check.lock').exists()
 assert not (H/'data/verification.json').exists() and not (H/'data/checkpoint.json').exists()
 names=['MATHEMATICAL_NOTE.md','data/proof-review.json','audit/proof-review.md',
        'data/certificate-audit.json','audit/certificate-review.md',
        'data/probe-audit.json','audit/probe-review.md',
        'data/coverage-audit.json','audit/coverage-review.md',
        'audit/graph-review.md','data/graph-26-25-25/results.json',
        'data/graph-26-25-25/saved-cycle-audit.json','data/graph-26-25-25/cycle-targets.json',
        'data/total341-plan.json','data/export-archive-audit.json',
        'audit/export-status-note.md','data/deficit-refinement.json','data/batch-observation.json']
 pins={p:sha(H/p) for p in names}
 v=dict(status=status,pins=pins,reviewed_modules=46,axiom_reports=22,
  closed_reversal_classes=['0123041'],native_negative_classes=19,unknown_classes=['0120310','0120324'],
  universal_floor25_proved=False,universal_floor26_proved=False,
  conditional_length_bounds=[234,233],conditional_deficit_budget=28,
  new_global_upper_bound=False,previous_goal_turn='PROGRESS',
  scope='One six-count direction class is proved for actual snakes in both orientations. Actual-snake conditional bounds and the 39-block deficit criterion are checked. The universal floor and deficit premises remain unproved. No new unconditional global upper bound.')
 (H/'data/verification.json').write_text(json.dumps(v,indent=2)+'\n')
 prior=R/'milestones/123-six-count-recovery/data/checkpoint.json'
 c=dict(status=status,verification_sha256=sha(H/'data/verification.json'),
  prior_checkpoint=prior.relative_to(R).as_posix(),prior_checkpoint_sha256=sha(prior),
  base_commit='14d55d96a02775dd08e8ae52f06cb7a26576a58e',paper_revision=116,next_paper_revision=126,
  paper_sha256=sha(paper),goal_status='ACTIVE',current_interval=[191,235],
  interval_scope='Maintained prior result with documented independent rebuild limitation; 234 and 233 require the stated additional hypotheses.',
  batches=obs['batches'])
 (H/'data/checkpoint.json').write_text(json.dumps(c,indent=2)+'\n')
 selected=[p for p in H.rglob('*') if p.is_file() and p!=manifest and '__pycache__' not in p.parts and p.suffix!='.lock']
 selected += [R/p for p in ['README.md','COLLABORATION.md','RESEARCH_LEDGER.md','milestones/README.md','handoff/README.md','handoff/CURRENT_STATUS.md','handoff/NEXT_AGENT_PROMPT.md']]
 rows=[dict(path=p.relative_to(R).as_posix(),bytes=p.stat().st_size,sha256=sha(p)) for p in sorted(set(selected))]
 assert all(x['bytes']<100000000 for x in rows)
 manifest.write_text(json.dumps(dict(status='SAVED_IMMUTABLE_SIX_COUNT_RESEARCH124',files=rows,
  scope='All saved milestone124 files and seven updated handover documents. Prior live proof batches remain separate.'),indent=2)+'\n')
 print('SAVED_MANIFEST',len(rows),sum(x['bytes'] for x in rows),'bytes')
else:
 v=read(H/'data/verification.json');c=read(H/'data/checkpoint.json')
 assert c['status']==v['status']==status
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
   if not name.startswith('milestones/124-'):raw=raw.replace(b'\r\n',b'\n')
   assert hashlib.sha1(b'blob '+str(len(raw)).encode()+b'\0'+raw).hexdigest()==blobs[name],name
 print('PASS_EXACT_STAGED_FILES' if '--staged' in sys.argv else 'PASS_LOCAL_MANIFEST',len(rows))
