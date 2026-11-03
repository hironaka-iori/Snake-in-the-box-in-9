"""Verify143 mathematical evidence and preserved partial share proof before publication."""
from pathlib import Path
import hashlib,json,os,re,subprocess,sys
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
q=read(H/'data/Range143-audit.json');src=H/'lean/Range143.lean'
assert q['status']=='PASS' and q['exit_code']==0 and not q.get('timeout')
assert sha(src)==q['source_sha256'] and len(q['axioms'])==7
assert all(set(a['axioms'])<={'propext','Classical.choice','Quot.sound'} for a in q['axioms'])
for k in ['object','importable_object','log']:assert sha(q[k])==q[k+'_sha256']
logdir=Path(q['log']).parent
assert sha(logdir/'source.lean.txt')==q['source_sha256'] and sha(logdir/'checker.py.txt')==q['checker_sha256']
pins(q,'dependencies')
native=read(H/'data/native-base.json');cert=H/'work/certificate-base'
assert native['status']=='PASS_COMPLETE_NATIVE_RUP_REPLAY'
assert (native['variables'],native['original_clauses'],native['core_clauses'],native['lemmas'],native['hints'])==(10616,88038,10078,29165,1699457)
assert native['replay']['every_trimmed_step_checked'] and native['replay']['final_empty_clause_checked']
pins(native)
for p,d in native['preserved_files_sha256'].items():assert sha(cert/p)==d
prep=read(H/'data/preparation.json');assert prep['share_cap']==12 and prep['bounds']==[[0,21]]*5 and prep['extra_cycle_cuts']==[]
pins(prep)
for n,status in [('native-input-review','PASS_INDEPENDENT_INPUT_CORE_AND_NATIVE_RUP_REVIEW'),('range-review','PASS_SAVED_CYCLE_AND_WALK_RANGE_REVIEW'),('range-analysis','PASS_EXACT_CYCLE_AND_SUBWALK_ARITHMETIC'),('cycle-range-attainment','PASS_CYCLE_ONLY_RANGE_ATTAINMENT')]:
 j=read(H/f'data/{n}.json');assert j['status']==status;pins(j)
plan=read(H/'data/proof-plan-base.json');assert len(plan['module_order'])==231 and plan['stats']['simulated'];pins(plan)
for a in plan['artifacts']:
 p=H/a['path'];assert sha(p)==a['sha256']
 assert not re.search(r'\b(sorry|admit|native_decide|axiom)\b',p.read_text(encoding='utf-8'))
stop=read(H/'data/intentional-stop.json');assert stop['status']=='INTENTIONALLY_STOPPED_SUPERSEDED_SHARE13_TARGET' and stop['checked_modules']==23
assert not (H/'data/replay-base.lock').exists()
for p,d in stop['snapshots'].items():assert sha(H/p)==d
progress=read(H/'data/replay-progress-base.json');assert len(progress['checked_modules'])==23
assert progress['active']['module']=='Share143.Shard19'
assert not (H/'data/Share143.Shard19-audit.json').exists()
share_reports=0
for item in progress['checked_modules']:
 m=item['module'];rp=H/'data'/(m+'-audit.json');r=read(rp)
 assert sha(rp)==item['receipt_sha256'] and r['exit_code']==0 and not r.get('timeout') and r['status']=='PASS_WINDOW_REPLAY_MODULE'
 assert sha(H/'lean'/(m.replace('.','/')+'.lean'))==r['source_sha256']==sha(H/r['source_snapshot'])
 assert sha(H/'build-base'/(m.replace('.','/')+'.olean'))==r['olean_sha256']
 assert sha(H/r['log'])==r['log_sha256'];pins(r,'dependencies')
 assert all(set(a['axioms'])<={'propext','Classical.choice','Quot.sound'} for a in r['theorem_audits']);share_reports+=len(r['theorem_audits'])
assert not (H/'data/Share143.Reversal-audit.json').exists()
paper=R/'paper/snake9_research.tex';editor=Path('D:/Codex/2026-10-13/new-chat/outputs/snake9_research.tex')
revision=read(H/'data/paper-revision.json');pr=read(H/'data/paper-source-review.json')
assert sha(paper)==sha(editor)==revision['after_sha256']==pr['source_sha256']
assert paper.read_bytes().split(b'\\begin{document}',1)[0]==(H/'audit/paper-before.tex.txt').read_bytes().split(b'\\begin{document}',1)[0]
assert revision['new_named_definitions']==0 and pr['definition_environment_count']==1
assert read(H/'data/latex-compilation.json')['status']=='INFRASTRUCTURE_FAILURE_BEFORE_TEX'
for row in read(H/'data/batch-observation.json')['batches']:
 assert sha(H/row['snapshot'])==row['sha256']
 if 'checker_snapshot' in row:assert sha(H/row['checker_snapshot'])==row['checker_snapshot_sha256']
g=['git','-c','core.commitGraph=false','-c','maintenance.auto=false','-c','gc.auto=0']
manifest=H/'data/file-manifest.json'
if not manifest.exists():
 assert len(sys.argv)==1 and subprocess.check_output(g+['rev-parse','HEAD'],cwd=R,text=True).strip()=='d29e9db3e5590942fbd4ba4a966e89b1f65870ab'
 verification=dict(status='PASS_RANGE_OBSTRUCTION_WITH_PRESERVED_PARTIAL_SHARE13_PROOF',range_lean_modules=1,range_axiom_reports=7,partial_share_modules=23,planned_share_modules=231,partial_share_axiom_reports=share_reports,share13_actual_theorem_complete=False,native_replay_deductions=29165,native_replay_hints=1699457,independent_native_replay=True,excluded_share_floors='At most14 in the fixed graph/comparison',comparison_lower_bound='4964197/21124',gap_from235='57/21124',first_floor_surviving_cycle_test=15,selected_next_share_floor=18,full_graph_recomputed=False,new_global_upper_bound=False,paper_sha256=sha(paper),new_named_definitions=0,pdf_rebuilt=False)
 (H/'data/verification.json').write_text(json.dumps(verification,indent=2)+'\n',encoding='utf-8')
 checkpoint=dict(status=verification['status'],goal_status='ACTIVE',previous_goal_turn='PROGRESS',base_commit='d29e9db3e5590942fbd4ba4a966e89b1f65870ab',prior_checkpoint_sha256=sha(R/'milestones/142-retuned-occurrence-credit/data/checkpoint.json'),verification_sha256=sha(H/'data/verification.json'),current_interval=[191,235],interval_scope='Maintained contributor upper proof with incomplete independent rebuilding.',selected_next_task='Count-free012034 share18 in a separate cap17 instance. Preserve stopped13 and old20 evidence; other conditional premises remain.',last_full_paper_revision=136,targeted_paper_revision=143,next_full_paper_revision=146,paper_sha256=sha(paper),pdf_rebuilt=False,live115_observed_modules=1203,total115_modules=1397,share13_replay_intentionally_stopped=True)
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
 manifest.write_text(json.dumps(dict(status='SAVED_RANGE_OBSTRUCTION_NATIVE_CERTIFICATE_PARTIAL_LEAN_AND_PAPER143',files=rows,excluded='Compiled objects remain local with hashes in receipts. Other live jobs appear only in frozen observations.'),indent=2)+'\n',encoding='utf-8')
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
  if not n.startswith('milestones/143-countfree-share13/'):expected=expected.replace(b'\r\n',b'\n')
  assert b==expected,n
 proc.stdin.close();assert proc.wait()==0
print(json.dumps(dict(status='PASS_STAGED' if '--staged' in sys.argv else 'PASS_SAVED',files=len(names),bytes=sum(x['bytes'] for x in j['files'])+manifest.stat().st_size,range_lean_reports=7,partial_share_modules=23,share13_actual_theorem_complete=False,new_global_upper_bound=False)))
