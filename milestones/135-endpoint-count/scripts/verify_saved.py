"""Check exact proof receipts and freeze the actual occurrence bound."""
from pathlib import Path
import datetime,hashlib,json,re,subprocess,sys
H=Path(__file__).resolve().parents[1];R=H.parents[1]
read=lambda p:json.loads(Path(p).read_text(encoding='utf-8-sig'))
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
modules={'EvenWindows135':3,'WindowSeparation135':4,'WindowCapacity135':1,
 'MissingDegree135':6,'ActualCount135':3}
reports=[]
for name,count in modules.items():
 q=read(H/'data'/(name+'-audit.json'))
 assert q['status']=='PASS' and q['exit_code']==0 and not q.get('timeout')
 source=H/'lean'/(name+'.lean');assert sha(source)==q['source_sha256']
 assert sha(Path(q['log']).parent/'source.lean.txt')==q['source_sha256']
 assert sha(Path(q['log']).parent/'checker.py.txt')==q['checker_sha256']
 for key in ['object','importable_object','log']:assert sha(q[key])==q[key+'_sha256']
 for n,d in q['dependencies'].items():
  p=Path(n);assert sha(p if p.is_absolute() else R/p)==d,n
 assert len(q['axioms'])==count
 assert all(set(x['axioms'])<={'propext','Classical.choice','Quot.sound'} for x in q['axioms'])
 assert not re.search(r'\b(sorry|admit|native_decide|axiom)\b',source.read_text(encoding='utf-8'))
 reports.extend(q['axioms'])
manifest=H/'data/file-manifest.json'
if not manifest.exists():
 assert len(sys.argv)==1
 paper=R/'paper/snake9_research.tex';editor=Path('D:/Codex/2026-10-13/new-chat/outputs/snake9_research.tex')
 assert sha(paper)==sha(editor)=='4667daec19f0b83af9fb129a263c8ae992757105414bad817c1ad13e1e11bb90'
 observation=read(H/'data/batch-observation.json')
 for row in observation['batches']:
  assert sha(H/row['snapshot'])==row['sha256']
  if 'checker_snapshot' in row:assert sha(H/row['checker_snapshot'])==row['checker_snapshot_sha256']
 verification=dict(status='PASS_ACTUAL_LOW_PAIR_OCCURRENCE_BOUND',recorded_at=datetime.datetime.now(datetime.timezone.utc).isoformat(),
  modules=list(modules),axiom_reports=len(reports),checked_per_endpoint_common_neighbor_bound=16,
  checked_total_low_pair_window_bound=32,actual_occurrence_bound_lean_checked=True,
  missing_degree_identities_lean_checked=True,written_per_endpoint_bound=12,
  written_total_bound=24,stronger_written_occurrence_bound_lean_checked=False,new_global_length_bound=False,
  scope='Actual low-pair windows have a checked total bound of 32. The stronger twelve-per-endpoint argument still requires maximal intervals and geometric assembly.')
 (H/'data/verification.json').write_text(json.dumps(verification,indent=2)+'\n',encoding='utf-8')
 checkpoint=dict(status=verification['status'],goal_status='ACTIVE',previous_goal_turn='PROGRESS',
  base_commit='20710ca7a4473c2147677a1ca6a55e2adcee1e02',
  prior_checkpoint_sha256=sha(R/'milestones/134-endpoint-geometry/data/checkpoint.json'),
  verification_sha256=sha(H/'data/verification.json'),batch_observation_sha256=sha(H/'data/batch-observation.json'),
  current_interval=[191,235],interval_scope='Maintained contributor result with incomplete independent upper-proof rebuild.',
  paper_revision=126,next_paper_revision=136,paper_sha256=sha(paper),
  selected_next_task='Construct maximal intervals and instantiate the degree sums for the stronger twelve-window endpoint estimate; revise the paper in round 136.')
 (H/'data/checkpoint.json').write_text(json.dumps(checkpoint,indent=2)+'\n',encoding='utf-8')
 selected={p for p in H.rglob('*') if p.is_file() and p!=manifest and '__pycache__' not in p.parts
  and p.suffix not in ['.tmp','.lock','.pending'] and p.name!='stage-paths.nul'}
 selected.update(R/n for n in ['README.md','COLLABORATION.md','RESEARCH_LEDGER.md','WORKSPACE.md',
  'milestones/README.md','handoff/README.md','handoff/CURRENT_STATUS.md','handoff/NEXT_AGENT_PROMPT.md'])
 rows=[dict(path=p.relative_to(R).as_posix(),bytes=p.stat().st_size,sha256=sha(p)) for p in sorted(selected)]
 assert all(x['bytes']<100000000 for x in rows)
 manifest.write_text(json.dumps(dict(status='SAVED_ACTUAL_OCCURRENCE_BOUND135',files=rows,
  excluded_live_outputs='Other milestones remain live locally; frozen process-backed observations are included.'),indent=2)+'\n',encoding='utf-8')
j=read(manifest)
for x in j['files']:
 p=R/x['path'];assert p.stat().st_size==x['bytes'] and sha(p)==x['sha256'],x['path']
names={x['path'] for x in j['files']}|{manifest.relative_to(R).as_posix()}
g=['git','-c','core.commitGraph=false','-c','maintenance.auto=false','-c','gc.auto=0']
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
  if not n.startswith('milestones/135-endpoint-count/'):expected=expected.replace(b'\r\n',b'\n')
  assert b==expected,n
 proc.stdin.close();assert proc.wait()==0
print(json.dumps(dict(status='PASS_STAGED' if '--staged' in sys.argv else 'PASS_SAVED',files=len(names),
 bytes=sum(x['bytes'] for x in j['files'])+manifest.stat().st_size,axiom_reports=len(reports),
 actual_occurrence_bound_lean_checked=True,checked_total_low_pair_window_bound=32,
 stronger_written_occurrence_bound_lean_checked=False,new_global_length_bound=False)))
