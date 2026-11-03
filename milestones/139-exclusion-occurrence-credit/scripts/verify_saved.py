"""Freeze exact139 evidence; no graph or theorem computation is repeated."""
from pathlib import Path
import hashlib,json,gzip,re,subprocess,sys
H=Path(__file__).resolve().parents[1];R=H.parents[1]
read=lambda p:json.loads(Path(p).read_text(encoding='utf-8-sig'))
def sha(p):
 d=hashlib.sha256()
 with Path(p).open('rb') as f:
  for b in iter(lambda:f.read(1048576),b''):d.update(b)
 return d.hexdigest()
modules=['Credit139','Obstruction139','OptimalCredit139'];reports=[]
for n in modules:
 p=H/'data'/(n+'-audit.json');q=read(p);src=H/'lean'/(n+'.lean')
 assert q['status']=='PASS' and q['exit_code']==0 and not q.get('timeout')
 assert sha(src)==q['source_sha256']
 assert not re.search(r'\b(sorry|admit|native_decide|axiom)\b',src.read_text(encoding='utf-8-sig'))
 for key in ['object','importable_object','log']:assert sha(q[key])==q[key+'_sha256']
 log=Path(q['log']).parent
 assert sha(log/'source.lean.txt')==q['source_sha256']
 assert sha(log/'checker.py.txt')==q['checker_sha256']
 for key,d in q['dependencies'].items():
  path=Path(key);assert sha(path if path.is_absolute() else R/path)==d,key
 assert len(q['axioms'])==2 and all(set(a['axioms'])<={'propext','Classical.choice','Quot.sound'} for a in q['axioms'])
 reports.extend(q['axioms'])
F=H/'data/exclusion-credit83';result=read(F/'results.json');run=read(F/'run-status.json')
assert result['status']==run['status']=='PASS_CONDITIONAL_FULL_GRAPH_EXACT_MINIMA' and run['returncode']==0
assert result['states']==1601856 and result['edges']==4661772 and result['occurrence_events_retained']==8846
assert result['new_full_nine_rejections_on_predecessor']==1
assert sha(H/'scripts/evaluate_graph.py')==result['script_sha256']==run['script_sha256']==sha(F/'evaluate_graph.exact.py')
assert [p['mean'] for p in result['profiles']]==['2446/5','496']
for profile in result['profiles']:
 assert profile['all_edge_inequalities_checked'] and profile['inequalities_checked']==4661772
 assert profile['comparison_integer_bound']==235 and not any(e['occurrence_event'] for e in profile['cycle'])
 raw=gzip.decompress((F/profile['potential_file']).read_bytes())
 assert len(raw)==8*1601856 and hashlib.sha256(raw).hexdigest()==profile['potential_sha256']
for record in [result,read(H/'data/result-review.json'),read(H/'data/critical-witness-screen.json')]:
 for key,d in record['source_files_sha256'].items():
  path=Path(key);assert sha(path if path.is_absolute() else R/path)==d,key
assert read(H/'data/result-review.json')['status']=='PASS_INDEPENDENT_SAVED_RESULT_REVIEW'
assert not read(H/'data/result-review.json')['all_edge_inequalities_independently_recomputed']
paper=R/'paper/snake9_research.tex';editor=Path('D:/Codex/2026-10-13/new-chat/outputs/snake9_research.tex')
revision=read(H/'data/paper-revision.json');review=read(H/'data/paper-source-review.json')
assert sha(paper)==sha(editor)==revision['after_sha256']==review['source_sha256']
assert revision['new_named_definitions']==0 and review['definition_environment_count']==1
assert paper.read_bytes().split(b'\\begin{document}',1)[0]==(H/'audit/paper-before.tex.txt').read_bytes().split(b'\\begin{document}',1)[0]
assert read(H/'data/latex-compilation.json')['status']=='INFRASTRUCTURE_FAILURE_BEFORE_TEX'
for row in read(H/'data/batch-observation.json')['batches']:
 assert sha(H/row['snapshot'])==row['sha256']
 if 'checker_snapshot' in row:assert sha(H/row['checker_snapshot'])==row['checker_snapshot_sha256']
g=['git','-c','core.commitGraph=false','-c','maintenance.auto=false','-c','gc.auto=0']
manifest=H/'data/file-manifest.json'
if not manifest.exists():
 assert len(sys.argv)==1
 assert subprocess.check_output(g+['rev-parse','HEAD'],cwd=R,text=True).strip()=='d59f82f7d30c348d768c90edf56754c5bc877e39'
 verification=dict(status='PASS_FINITE_GRAPH_REVIEW_AND_LEAN_UNIFORM_CREDIT_LIMITS',
  lean_modules=modules,axiom_reports=6,completed_mean='2446/5',conditional_mean='496',
  graph_edges=4661772,all_edge_scan_by_evaluator=True,independent_all_edge_scan=False,
  independent_saved_result_review=True,completed_arithmetic_relaxation_minimum='2757328/11723',
  zero_credit_cycle_lengths=[5,6],actual_suffix_occurrence_limit_checked=24,
  new_global_upper_bound=False,paper_sha256=sha(paper),new_named_definitions=0,pdf_rebuilt=False)
 (H/'data/verification.json').write_text(json.dumps(verification,indent=2)+'\n',encoding='utf-8')
 checkpoint=dict(status=verification['status'],goal_status='ACTIVE',previous_goal_turn='PROGRESS',
  base_commit='d59f82f7d30c348d768c90edf56754c5bc877e39',
  prior_checkpoint_sha256=sha(R/'milestones/138-seven-cycle-endpoints/data/checkpoint.json'),
  verification_sha256=sha(H/'data/verification.json'),current_interval=[191,235],
  interval_scope='Maintained contributor upper result with incomplete independent rebuild.',
  selected_next_task='Bounded actual-path feasibility of canonical012032 with exact internal counts3,5,4,5,3; no assumption that it forces an endpoint.',
  last_full_paper_revision=136,targeted_paper_revision=139,next_full_paper_revision=146,
  paper_sha256=sha(paper),pdf_rebuilt=False,live115_observed_modules=1056,total115_modules=1397)
 (H/'data/checkpoint.json').write_text(json.dumps(checkpoint,indent=2)+'\n',encoding='utf-8')
 selected={p for p in H.rglob('*') if p.is_file() and p!=manifest and '__pycache__' not in p.parts and p.suffix not in ['.tmp','.lock','.pending'] and p.name!='stage-paths.nul'}
 selected.update(R/n for n in ['README.md','COLLABORATION.md','RESEARCH_LEDGER.md','WORKSPACE.md','milestones/README.md','handoff/README.md','handoff/CURRENT_STATUS.md','handoff/NEXT_AGENT_PROMPT.md','paper/snake9_research.tex'])
 rows=[dict(path=p.relative_to(R).as_posix(),bytes=p.stat().st_size,sha256=sha(p)) for p in sorted(selected)]
 assert all(row['bytes']<100000000 for row in rows)
 manifest.write_text(json.dumps(dict(status='SAVED_UNIFORM_CREDIT_LIMIT_AND_PAPER139',files=rows,excluded_live_outputs='Other milestone jobs remain live; only frozen process observations are included.'),indent=2)+'\n',encoding='utf-8')
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
  if not n.startswith('milestones/139-exclusion-occurrence-credit/'):expected=expected.replace(b'\r\n',b'\n')
  assert b==expected,n
 proc.stdin.close();assert proc.wait()==0
print(json.dumps(dict(status='PASS_STAGED' if '--staged' in sys.argv else 'PASS_SAVED',files=len(names),bytes=sum(x['bytes'] for x in j['files'])+manifest.stat().st_size,lean_modules=3,axiom_reports=6,new_global_upper_bound=False)))
