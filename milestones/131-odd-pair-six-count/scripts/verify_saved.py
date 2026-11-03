"""Verify and preserve the finite-model experiment without upgrading its scope."""
from pathlib import Path
from fractions import Fraction
import datetime,gzip,hashlib,json,subprocess,sys
H=Path(__file__).resolve().parents[1];R=H.parents[1]
read=lambda p:json.loads(p.read_text(encoding='utf-8-sig'))
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
def pins(rows):
 for n,d in rows.items():
  p=Path(n);assert sha(p if p.is_absolute() else R/p)==d,n
F=H/'data/odd-pair9-six25'
result=read(F/'results.json');run=read(F/'run-status.json')
assert result['status']==run['status']=='PASS_CONDITIONAL_FULL_GRAPH_EXACT_MINIMA'
assert run['returncode']==0
assert sha(H/'scripts/evaluate_graph.py')==sha(F/'evaluate_graph.exact.py')==result['script_sha256']==run['script_sha256']
assert not (H/'data/fullgraph.lock').exists()
pins(result['source_files_sha256'])
for row in result['profiles']:
 assert read(F/(row['profile']+'-profile.json'))==row
 assert row['all_edge_inequalities_checked'] and row['cycle_attaining']
 assert row['inequalities_checked']==result['edges'] and row['minimum_slack']==0
 cycle=row['cycle']
 assert all(cycle[i]['v']==cycle[(i+1)%len(cycle)]['u'] for i in range(len(cycle)))
 assert Fraction(sum(x['weight'] for x in cycle),len(cycle))==Fraction(row['mean'])
 assert all(x['pair_bonus24']==x['six_bonus24']==0 and not x['six_shape_matches'] for x in cycle)
 raw=gzip.decompress((F/row['potential_file']).read_bytes())
 assert len(raw)==8*result['states'] and hashlib.sha256(raw).hexdigest()==row['potential_sha256']
 p,d=Fraction(row['mean']).numerator,Fraction(row['mean']).denominator
 assert Fraction(1098960*d+8*p+row['range_scaled'],4200*d+p)==Fraction(row['comparison_bound'])
 assert int(Fraction(row['comparison_bound']))==row['comparison_integer_bound']
 assert Fraction(1098960*d+8*p,4200*d+p)==Fraction(row['zero_range_comparison'])
 del raw
review=read(H/'data/graph-review.json');screen=read(H/'data/endpoint9-witness-screen.json')
assert review['status']=='PASS_STATIC_AND_INDEPENDENT_SAVED_CYCLE_REVIEW'
assert review['all_edge_algorithm_reviewed'] and not review['all_edge_inequalities_independently_recomputed']
pins(review['source_files_sha256']);pins(screen['source_files_sha256'])
assert sha(H/'audit/screen_endpoint9.py')==screen['script_sha256']
assert screen['witnesses_checked']==screen['distinct_exact_vertex_sequences_checked']==133
assert screen['canonical_windows_checked']==54 and screen['pair9_windows_checked']==0
assert screen['qualifying_window_screen_is_vacuous'] and screen['counterexample'] is None
task=read(H/'data/next-endpoint-task.json');pins(task['source_files_sha256'])
assert len(task['common_vertices'])==14 and not task['hypothesis_proved']
manifest=H/'data/file-manifest.json'
if not manifest.exists():
 assert len(sys.argv)==1
 paper=R/'paper/snake9_research.tex';editor=Path('D:/Codex/2026-10-13/new-chat/outputs/snake9_research.tex')
 assert sha(paper)==sha(editor)=='4667daec19f0b83af9fb129a263c8ae992757105414bad817c1ad13e1e11bb90'
 verification=dict(status='PASS_FINITE_GRAPH_AND_SINGLE_PATTERN_OBSTRUCTION',
  recorded_at=datetime.datetime.now(datetime.timezone.utc).isoformat(),
  result_sha256=sha(F/'results.json'),review_sha256=sha(H/'data/graph-review.json'),
  states=result['states'],edges=result['edges'],minimum_means=[p['mean'] for p in result['profiles']],
  integer_comparisons=[p['comparison_integer_bound'] for p in result['profiles']],
  evaluator_all_edges_checked=True,independent_cycle_rows_checked=True,
  independent_second_all_edge_check=False,new_lean_theorem=False,new_global_bound=False,
  raising_only_0123104_floor_cannot_improve_fixed_model_minima=True,
  witness_screen_vacuous=True,next_endpoint_hypothesis_proved=False,
  scope='Exact native finite-model results under inherited unproved hypotheses. No actual-snake bound.')
 (H/'data/verification.json').write_text(json.dumps(verification,indent=2)+'\n',encoding='utf-8')
 checkpoint=dict(status=verification['status'],goal_status='ACTIVE',previous_goal_turn='PROGRESS',
  base_commit='9871042cfdbce447d00615f0576cf165ea317025',
  prior_checkpoint_sha256=sha(R/'milestones/130-fourth-count-large/data/checkpoint.json'),
  verification_sha256=sha(H/'data/verification.json'),batch_observation_sha256=sha(H/'data/batch-observation.json'),
  current_interval=[191,235],interval_scope='Maintained contributor result with incomplete independent upper-proof rebuild.',
  paper_revision=126,next_paper_revision=136,paper_sha256=sha(paper),
  selected_next_task='Direct falsification of the odd-length pair9 endpoint hypothesis.')
 (H/'data/checkpoint.json').write_text(json.dumps(checkpoint,indent=2)+'\n',encoding='utf-8')
 selected={p for p in H.rglob('*') if p.is_file() and p!=manifest and '__pycache__' not in p.parts
  and p.suffix not in ['.tmp','.lock'] and p.name!='stage-paths.nul'}
 selected.update(R/n for n in ['README.md','COLLABORATION.md','RESEARCH_LEDGER.md','WORKSPACE.md',
  'milestones/README.md','handoff/README.md','handoff/CURRENT_STATUS.md','handoff/NEXT_AGENT_PROMPT.md'])
 rows=[dict(path=p.relative_to(R).as_posix(),bytes=p.stat().st_size,sha256=sha(p)) for p in sorted(selected)]
 assert all(x['bytes']<100000000 for x in rows)
 manifest.write_text(json.dumps(dict(status='SAVED_FINITE_GRAPH_EXPERIMENT131',files=rows,
  excluded_live_outputs='Other milestones live progress remains local; frozen batch observations are included.'),indent=2)+'\n',encoding='utf-8')
j=read(manifest)
for x in j['files']:
 p=R/x['path'];assert p.stat().st_size==x['bytes'] and sha(p)==x['sha256'],x['path']
names={x['path'] for x in j['files']}|{manifest.relative_to(R).as_posix()}
g=['git','-c','core.commitGraph=false','-c','maintenance.auto=false','-c','gc.auto=0']
if '--stage' in sys.argv:
 assert not subprocess.check_output(g+['diff','--cached','--name-only'],cwd=R).strip()
 path=H/'data/stage-paths.nul';path.write_bytes(b''.join(n.encode()+b'\0' for n in sorted(names)))
 subprocess.run(g+['add','-f','--pathspec-from-file='+str(path),'--pathspec-file-nul'],cwd=R,check=True)
if '--staged' in sys.argv:
 actual=set(subprocess.check_output(g+['diff','--cached','--name-only','-z'],cwd=R).decode().strip('\0').split('\0'));assert actual==names
 proc=subprocess.Popen(g+['cat-file','--batch'],cwd=R,stdin=subprocess.PIPE,stdout=subprocess.PIPE)
 for name in sorted(names):
  proc.stdin.write((':'+name+'\n').encode());proc.stdin.flush();header=proc.stdout.readline().decode().split();assert header[1]=='blob'
  b=proc.stdout.read(int(header[2]));assert proc.stdout.read(1)==b'\n'
  expected=(R/name).read_bytes()
  if not name.startswith('milestones/131-odd-pair-six-count/'):expected=expected.replace(b'\r\n',b'\n')
  assert b==expected,name
 proc.stdin.close();assert proc.wait()==0
print(json.dumps(dict(status='PASS_STAGED' if '--staged' in sys.argv else 'PASS_SAVED',files=len(names),
 bytes=sum(x['bytes'] for x in j['files'])+manifest.stat().st_size,new_global_bound=False)))
