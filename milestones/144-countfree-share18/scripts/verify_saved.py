"""Verify exact milestone144 evidence and stage only the publication manifest."""
from pathlib import Path
import gzip,hashlib,json,os,re,subprocess,sys
H=Path(__file__).resolve().parents[1];R=H.parents[1]
read=lambda p:json.loads(Path(p).read_text(encoding='utf-8-sig'))
cache={}
def sha(p):
 p=Path(p);key=(str(p.resolve()),p.stat().st_size,p.stat().st_mtime_ns)
 if key not in cache:
  d=hashlib.sha256()
  with p.open('rb') as f:
   for b in iter(lambda:f.read(1048576),b''):d.update(b)
  cache[key]=d.hexdigest()
 return cache[key]
def pins(j,key='source_files_sha256'):
 for p,d in j.get(key,{}).items():assert sha(Path(p) if Path(p).is_absolute() else R/p)==d,p
prep=read(H/'data/preparation.json');assert prep['share_cap']==17 and prep['bounds']==[[0,21]]*5 and prep['extra_cycle_cuts']==[];pins(prep)
native=read(H/'data/native-alternative.json');assert native['status']=='NATIVE_REPLAY_PENDING_HINT_LIMIT'
assert (native['variables'],native['original_clauses'],native['core_clauses'],native['lemmas'],native['hints'])==(11924,96091,13224,145215,14710881)
pins(native)
for p,d in native['preserved_files_sha256'].items():assert sha(H/'work/certificate-alternative'/p)==d
review=read(H/'data/alternative-review.json');assert review['status']=='PASS_INDEPENDENT_ALTERNATIVE_CORE_AND_RUP_REVIEW'
assert review['replay']['final_empty_clause'] and review['replay']['hints']==14710881;pins(review,'sources_sha256')
for name,status in [('export-review','PASS_BOUNDED_EXPORT_SOURCE_AND_TRANSPORT_REVIEW_LEAN_PENDING'),('graph-review','PASS_BOUNDED_GRAPH_CYCLE_REVIEW'),('retuned-review','PASS_BOUNDED_RETUNED_CYCLE_REVIEW')]:
 j=read(H/f'data/{name}.json');assert j['status']==status;pins(j);pins(j,'sources_sha256')
plan=read(H/'data/proof-plan-base.json');assert len(plan['module_order'])==1324 and plan['stats']['simulated'];pins(plan)
for x in plan['artifacts']:
 p=H/x['path'];assert sha(p)==x['sha256']
 assert not re.search(r'\b(sorry|admit|native_decide|axiom)\b',p.read_text(encoding='utf-8'))
stop=read(H/'data/warmup-stop.json');assert stop['checked_modules']==6 and stop['status']=='INTENTIONALLY_STOPPED_FIRST_CHECK_MEMORY_PRESSURE'
assert not (H/'data/replay-base.lock').exists() and not (H/'data/fullgraph.lock').exists()
progress=read(H/'data/replay-progress-base.json');assert len(progress['checked_modules'])==6
for item in progress['checked_modules']:
 m=item['module'];rp=H/'data'/(m+'-audit.json');q=read(rp)
 assert sha(rp)==item['receipt_sha256'] and q['exit_code']==0 and q['status']=='PASS_WINDOW_REPLAY_MODULE'
 assert sha(H/'lean'/(m.replace('.','/')+'.lean'))==q['source_sha256']==sha(H/q['source_snapshot'])
 assert sha(H/'build-base'/(m.replace('.','/')+'.olean'))==q['olean_sha256']
 assert sha(H/q['log'])==q['log_sha256'];pins(q,'dependencies')
 assert all(set(x['axioms'])<={'propext','Classical.choice','Quot.sound'} for x in q['theorem_audits'])
reports=0
for m,count in [('RawInit144',2),('Obstruction144',9),('RetunedObstruction144',5),('LiteralData144',0),('LiteralSmall144',1),('LiteralProbe144',1)]:
 q=read(H/'experiments/data'/(m+'-audit.json'));assert q['status']=='PASS' and q['exit_code']==0 and q['stop_reason'] is None
 assert sha(q['source'])==q['source_sha256'] and sha(q['object'])==q['olean_sha256'] and sha(q['log'])==q['log_sha256']
 ld=Path(q['log']).parent;assert sha(ld/'source.lean.txt')==q['source_sha256'] and sha(ld/'checker.py.txt')==q['checker_sha256']
 assert len(q['axioms'])==count and all(set(x['axioms'])<={'propext','Classical.choice','Quot.sound'} for x in q['axioms']);reports+=count
 pins(q,'dependencies')
assert not read(H/'experiments/data/literal-preparation.json')['initial_tree_validity_proof_complete']
for label,mean,spread,bound in [('share18-impact','5399/11','593','12138275/51599'),('share18-credit601-over36','3445/7','608','23182022/98535')]:
 j=read(H/'data'/label/'results.json');assert j['status']=='PASS_CONDITIONAL_FULL_GRAPH_EXACT_MINIMA';pins(j)
 q=j['profiles'][0];assert (q['mean'],q['range'],q['comparison_bound'])==(mean,spread,bound)
 assert q['all_edge_inequalities_checked'] and q['inequalities_checked']==4661572
 assert hashlib.sha256(gzip.decompress((H/'data'/label/q['potential_file']).read_bytes())).hexdigest()==q['potential_sha256']
archives=read(H/'data/large-proof-archives.json')['files']+[read(H/'data/timeout-archive.json')]
excluded=set()
for x in archives:
 source=H/x['source'];archive=H/x['archive'];excluded.add(source)
 assert sha(source)==x['source_sha256'] and sha(archive)==x['archive_sha256']
 d=hashlib.sha256();n=0
 with gzip.open(archive,'rb') as f:
  for b in iter(lambda:f.read(1048576),b''):d.update(b);n+=len(b)
 assert d.hexdigest()==x['source_sha256'] and n==x['source_bytes']
paper=R/'paper/snake9_research.tex';editor=Path('D:/Codex/2026-10-13/new-chat/outputs/snake9_research.tex')
pr=read(H/'data/paper-source-review.json');rev=read(H/'data/paper-revision.json')
assert sha(paper)==sha(editor)==pr['source_sha256']==rev['after_sha256']
assert paper.read_bytes().split(b'\\begin{document}',1)[0]==(H/'audit/paper-before.tex.txt').read_bytes().split(b'\\begin{document}',1)[0]
assert pr['definition_environment_count']==1 and rev['new_named_definitions']==0
assert read(H/'data/compilation.json')['status']=='FAILED_BEFORE_TEX_PREPARATION'
for row in read(H/'data/batch-observation.json')['batches']:
 assert sha(H/row['snapshot'])==row['sha256']
 if 'checker_snapshot' in row:assert sha(H/row['checker_snapshot'])==row['checker_snapshot_sha256']
pins(read(H/'data/next-task.json'))
g=['git','-c','core.commitGraph=false','-c','maintenance.auto=false','-c','gc.auto=0']
manifest=H/'data/file-manifest.json'
if not manifest.exists():
 assert len(sys.argv)==1 and subprocess.check_output(g+['rev-parse','HEAD'],cwd=R,text=True).strip()=='55ff9e0fe0355e549edc699dbf427517dd71fc61'
 v=dict(status='PASS_SAVED_NATIVE_SHARE18_CERTIFICATE_AND_TWO_PARAMETER_OBSTRUCTION',native_deductions=145215,native_hints=14710881,
  original_lean_modules_passed=6,original_lean_modules_planned=1324,experiment_axiom_reports=reports,arithmetic_reports=14,
  literal_initial_tree_truth_bridge_complete=False,share18_actual_theorem_complete=False,
  comparison_lower_bound='1544056/6569',obstruction_scope='Arbitrary012034 floor and uniform occurrence credit, fixed other graph weights/edges',
  graph_all_edge_checks='producer',independent_graph_checks='bounded source cycles and potential ranges',new_global_upper_bound=False,
  selected_next_shape='012301',selected_floor=16,paper_sha256=sha(paper),pdf_rebuilt=False)
 (H/'data/verification.json').write_text(json.dumps(v,indent=2)+'\n')
 checkpoint=dict(status=v['status'],goal_status='ACTIVE',previous_goal_turn='PROGRESS',base_commit='55ff9e0fe0355e549edc699dbf427517dd71fc61',
  verification_sha256=sha(H/'data/verification.json'),prior_checkpoint_sha256=sha(R/'milestones/143-countfree-share13/data/checkpoint.json'),
  current_interval=[191,235],interval_scope='Maintained contributor proof; independent rebuild incomplete.',selected_next_task='012301 count-free share16; locate and validate old native proof, complete literal-initial-tree truth bridge before full replay.',
  last_full_paper_revision=136,targeted_paper_revision=144,next_full_paper_revision=146,paper_sha256=sha(paper),pdf_rebuilt=False,
  live115_observed_modules=1287,total115_modules=1397,all144_jobs_complete_or_stopped=True)
 (H/'data/checkpoint.json').write_text(json.dumps(checkpoint,indent=2)+'\n')
 selected=set()
 for folder,dirs,files in os.walk(H,followlinks=False):
  dirs[:]=[n for n in dirs if not n.startswith('build') and n!='__pycache__']
  for n in files:
   p=Path(folder)/n
   if p==manifest or p in excluded or p.suffix in ['.tmp','.pending','.lock','.olean','.ilean'] or n=='stage-paths.nul':continue
   selected.add(p)
 selected.update(R/n for n in ['README.md','COLLABORATION.md','RESEARCH_LEDGER.md','WORKSPACE.md','milestones/README.md','handoff/README.md','handoff/CURRENT_STATUS.md','handoff/NEXT_AGENT_PROMPT.md','paper/snake9_research.tex'])
 rows=[dict(path=p.relative_to(R).as_posix(),bytes=p.stat().st_size,sha256=sha(p)) for p in sorted(selected)]
 assert all(x['bytes']<100000000 for x in rows)
 manifest.write_text(json.dumps(dict(status='EXACT_144_PUBLICATION_MANIFEST',files=rows,excluded_large_originals=[p.relative_to(H).as_posix() for p in sorted(excluded)],note='All large originals retained locally and published as byte-exact gzip archives; compiled objects retained locally with receipt hashes.'),indent=2)+'\n')
j=read(manifest)
for x in j['files']:
 p=R/x['path'];assert p.stat().st_size==x['bytes'] and sha(p)==x['sha256'],x['path']
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
  if not n.startswith('milestones/144-countfree-share18/'):expected=expected.replace(b'\r\n',b'\n')
  assert b==expected,n
 proc.stdin.close();assert proc.wait()==0
print(json.dumps(dict(status='PASS_STAGED' if '--staged' in sys.argv else 'PASS_SAVED',files=len(names),bytes=sum(x['bytes'] for x in j['files'])+manifest.stat().st_size,actual_share18_theorem_complete=False,new_global_upper_bound=False)))
