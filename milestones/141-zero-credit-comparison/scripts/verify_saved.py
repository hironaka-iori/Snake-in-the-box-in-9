"""Freeze the exact zero-credit evidence and paper141; no graph calculation is rerun."""
from pathlib import Path
import gzip,hashlib,json,os,re,subprocess,sys
H=Path(__file__).resolve().parents[1];R=H.parents[1]
read=lambda p:json.loads(Path(p).read_text(encoding='utf-8-sig'))
def sha(p):
 d=hashlib.sha256()
 with Path(p).open('rb') as f:
  for b in iter(lambda:f.read(1048576),b''):d.update(b)
 return d.hexdigest()
q=read(H/'data/Comparison141-audit.json');src=H/'lean/Comparison141.lean'
assert q['status']=='PASS' and q['exit_code']==0 and not q.get('timeout')
assert sha(src)==q['source_sha256']
assert not re.search(r'\b(sorry|admit|native_decide|axiom)\b',src.read_text(encoding='utf-8'))
assert len(q['axioms'])==8 and all(set(a['axioms'])<={'propext','Classical.choice','Quot.sound'} for a in q['axioms'])
for key in ['object','importable_object','log']:assert sha(q[key])==q[key+'_sha256']
logdir=Path(q['log']).parent
assert sha(logdir/'source.lean.txt')==q['source_sha256'] and sha(logdir/'checker.py.txt')==q['checker_sha256']
for p,d in q['dependencies'].items():assert sha(Path(p) if Path(p).is_absolute() else R/p)==d,p
folder=H/'data/five-cycle-zero';result=read(folder/'results.json');run=read(folder/'run-status.json')
assert result['status']==run['status']=='PASS_CONDITIONAL_FULL_GRAPH_EXACT_MINIMA' and run['returncode']==0
assert result['states']==1601856 and result['edges']==4661572 and result['credit']=='0' and result['weight_multiplier']==1
assert result['new_weak_exclusion']['removed_from139']==200 and result['predecessor139_reproduced']
assert sha(H/'scripts/evaluate_graph.py')==result['script_sha256']==run['script_sha256']==sha(folder/'evaluate_graph.exact.py')
expected=[('3424/7','4159/7','7724271/32824',235),('496','602','551765/2348',234)]
for p,values in zip(result['profiles'],expected):
 assert (p['mean'],p['range'],p['comparison_bound'],p['comparison_integer_bound'])==values
 assert p['all_edge_inequalities_checked'] and p['inequalities_checked']==4661572 and p['cycle_attaining']
 assert not any(e['occurrence_credit_scaled'] for e in p['cycle'])
 raw=gzip.decompress((folder/p['potential_file']).read_bytes());assert len(raw)==8*1601856 and hashlib.sha256(raw).hexdigest()==p['potential_sha256']
review=read(H/'data/result-review.json');source_review=read(H/'data/zero-credit-source-review.json');next_credit=read(H/'data/next-credit.json')
assert review['status']=='PASS_BOUNDED_SAVED_RESULT_REVIEW' and review['selected_original_rows']==221 and review['new_removed_count']==200
assert review['all_new_removed_rows_satisfy_weak_exclusion'] and not review['independent_all_edge_potential_scan'] and not review['potential_range_optimality_established']
assert source_review['status']=='PASS_SOURCE_REVIEW_RESULT_AVAILABLE'
assert next_credit['candidate_credit']=='533/12' and next_credit['strict_range_threshold']=='5341/6' and next_credit['old18_survives']
for j in [result,review,source_review,next_credit]:
 for p,d in j['source_files_sha256'].items():assert sha(Path(p) if Path(p).is_absolute() else R/p)==d,p
paper=R/'paper/snake9_research.tex';editor=Path('D:/Codex/2026-10-13/new-chat/outputs/snake9_research.tex')
revision=read(H/'data/paper-revision.json');paper_review=read(H/'data/paper-source-review.json')
assert sha(paper)==sha(editor)==revision['after_sha256']==paper_review['source_sha256']
assert paper.read_bytes().split(b'\\begin{document}',1)[0]==(H/'audit/paper-before.tex.txt').read_bytes().split(b'\\begin{document}',1)[0]
assert revision['new_named_definitions']==0 and paper_review['definition_environment_count']==1
assert read(H/'data/latex-compilation.json')['status']=='INFRASTRUCTURE_FAILURE_BEFORE_TEX'
for row in read(H/'data/batch-observation.json')['batches']:
 assert sha(H/row['snapshot'])==row['sha256']
 if 'checker_snapshot' in row:assert sha(H/row['checker_snapshot'])==row['checker_snapshot_sha256']
g=['git','-c','core.commitGraph=false','-c','maintenance.auto=false','-c','gc.auto=0']
manifest=H/'data/file-manifest.json'
if not manifest.exists():
 assert len(sys.argv)==1
 assert subprocess.check_output(g+['rev-parse','HEAD'],cwd=R,text=True).strip()=='9f78ac76958cf146d1a90cd0a5743894a5f38284'
 verification=dict(status='PASS_ZERO_CREDIT_FINITE_GRAPH_AND_COMPARISON_LOGIC',lean_modules=1,axiom_reports=8,
 graph_edges=4661572,new_proved_deletions=200,all_edge_scan_by_evaluator=True,independent_all_edge_scan=False,independent_selected_rows=221,
 completed_mean='3424/7',completed_range='4159/7',completed_comparison='7724271/32824',conditional_mean='496',conditional_range='602',conditional_comparison='551765/2348',conditional_integer_comparison=234,
 next_credit='533/12',next_target_mean='3011/6',next_strict_range_threshold='5341/6',new_global_upper_bound=False,paper_sha256=sha(paper),new_named_definitions=0,pdf_rebuilt=False)
 (H/'data/verification.json').write_text(json.dumps(verification,indent=2)+'\n',encoding='utf-8')
 checkpoint=dict(status=verification['status'],goal_status='ACTIVE',previous_goal_turn='PROGRESS',base_commit='9f78ac76958cf146d1a90cd0a5743894a5f38284',prior_checkpoint_sha256=sha(R/'milestones/140-five-cycle-window/data/checkpoint.json'),verification_sha256=sha(H/'data/verification.json'),current_interval=[191,235],interval_scope='Maintained contributor upper proof with incomplete independent rebuilding.',selected_next_task='Completed-share uniform credit533/12; test target mean3011/6 and range<5341/6. Retain zero-credit additional-share comparison.',last_full_paper_revision=136,targeted_paper_revision=141,next_full_paper_revision=146,paper_sha256=sha(paper),pdf_rebuilt=False,live115_observed_modules=1127,total115_modules=1397)
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
 manifest.write_text(json.dumps(dict(status='SAVED_ZERO_CREDIT_RESULT_AND_PAPER141',files=rows,excluded='Build objects remain local with hashes in receipts; only frozen observations of other live milestones are included.'),indent=2)+'\n',encoding='utf-8')
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
  if not n.startswith('milestones/141-zero-credit-comparison/'):expected=expected.replace(b'\r\n',b'\n')
  assert b==expected,n
 proc.stdin.close();assert proc.wait()==0
print(json.dumps(dict(status='PASS_STAGED' if '--staged' in sys.argv else 'PASS_SAVED',files=len(names),bytes=sum(x['bytes'] for x in j['files'])+manifest.stat().st_size,lean_modules=1,axiom_reports=8,new_global_upper_bound=False)))
