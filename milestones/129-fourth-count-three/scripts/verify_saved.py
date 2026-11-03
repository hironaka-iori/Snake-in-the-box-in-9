"""Save and verify an exact, explicitly incomplete proof checkpoint."""
from pathlib import Path
import gzip, hashlib, json, subprocess, sys, datetime, tarfile
H=Path(__file__).resolve().parents[1];R=H.parents[1]
read=lambda p:json.loads(p.read_text(encoding='utf-8-sig'))
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
def pins(rows):
 for name,digest in rows.items():
  p=Path(name);assert sha(p if p.is_absolute() else R/p)==digest,name
def stream_hash(f):
 h=hashlib.sha256();n=0
 for b in iter(lambda:f.read(1048576),b''):h.update(b);n+=len(b)
 return h.hexdigest(),n
arc=read(H/'data/archives.json');originals=set()
for x in arc['files']:
 p=H/x['archive'];assert sha(p)==x['archive_sha256'];originals.add(H/x['original'])
 with gzip.open(p,'rb') as f:assert stream_hash(f)==(x['original_sha256'],x['original_bytes'])
 if '--restore-archives' in sys.argv and not (H/x['original']).exists():
  dest=H/x['original'];dest.parent.mkdir(parents=True,exist_ok=True)
  with gzip.open(p,'rb') as f,dest.open('xb') as out:
   for b in iter(lambda:f.read(1048576),b''):out.write(b)
endpoints=read(H/'data/endpoint122-archives.json')
assert sha(H/'data/endpoint122-completion-review.json')==endpoints['review_sha256']
assert sha(H/'scripts/archive_endpoint122.py')==endpoints['script_sha256']
for row in endpoints['archives']:
 p=H/row['path'];assert sha(p)==row['sha256']
 with tarfile.open(p,'r:gz') as tar:
  members=tar.getmembers();assert [m.name for m in members]==[x['path'] for x in row['files']]
  for member,x in zip(members,row['files']):
   dest=(R/x['path']).resolve();assert dest.is_relative_to((R/'milestones/122-endpoint-equality').resolve())
   assert member.isfile() and member.size==x['bytes']
   with tar.extractfile(member) as f:b=f.read()
   assert hashlib.sha256(b).hexdigest()==x['sha256']
   if dest.exists():assert sha(dest)==x['sha256']
   elif '--restore-archives' in sys.argv:
    dest.parent.mkdir(parents=True,exist_ok=True)
    with dest.open('xb') as f:f.write(b)
manifest=H/'data/file-manifest.json'
if not manifest.exists():
 assert len(sys.argv)==1
 for name in ['branch-review','transport-review','export-review','endpoint122-completion-review']:
  q=read(H/'data'/(name+'.json'));assert q['status'].startswith('PASS_');pins(q['source_files_sha256'])
 plan=read(H/'data/proof-plan.json')
 assert plan['stats']['simulated'] and (plan['stats']['lemmas'],plan['stats']['hints'])==(50082,2628221)
 for x in plan['artifacts']:assert sha(H/x['path'])==x['sha256']
 raw=(H/'data/replay-progress.json').read_bytes();replay=json.loads(raw)
 observed=H/'audit/observed-replay129.json';assert not observed.exists();observed.write_bytes(raw)
 assert replay['status']!='PASS_COMPLETE_CNF_REFUTATION','Complete actual assembly before changing proof status.'
 ps=json.loads(subprocess.check_output(['powershell','-NoProfile','-Command',"@(Get-CimInstance Win32_Process | Where-Object {$_.Name -in @('python.exe','lean.exe','lake.exe')} | Select-Object ProcessId,ParentProcessId,Name,CommandLine)|ConvertTo-Json -Compress"],text=True))
 if isinstance(ps,dict):ps=[ps]
 driver=next((p for p in ps if p['ProcessId']==replay['pid']),None)
 if replay['status'] in ['RUNNING','WAITING_FOR_RESOURCES','WAITING_FOR_CNF_RECEIPT']:
  assert driver is not None and '129-fourth-count-three' in driver['CommandLine']
 selected=set();independent=[]
 for rp in (H/'logs').glob('*/record.json'):
  q=read(rp);assert q['status']!='COMPILING',str(rp)
  if q['status']=='PASS':
   pins(q['dependencies']);assert q['exit_code']==0 and not q.get('timeout',False)
   for k in ['object','importable_object','log']:assert sha(Path(q[k]))==q[k+'_sha256']
   assert sha(rp.parent/'source.lean.txt')==q['source_sha256']
   assert sha(rp.parent/'checker.py.txt')==q['checker_sha256']
   ax=q.get('axioms',[]);assert all(set(a['axioms'])<={'propext','Classical.choice','Quot.sound'} for a in ax)
   independent.append(dict(module=Path(q['importable_object']).stem,receipt=rp.relative_to(H).as_posix(),sha256=sha(rp),reports=len(ax)))
  selected.update(p for p in rp.parent.rglob('*') if p.is_file())
 for x in replay['checked_modules']:
  m=x['module'];cnf=m=='Recovered129G.LocalWindowCnf.Triple129'
  rp=H/'data'/('independent-core-cnf-audit.json' if cnf else m+'-audit.json');q=read(rp)
  assert sha(rp)==x['receipt_sha256'] and q['exit_code']==0 and not q.get('timeout',False)
  pins(q['dependencies']);src=H/'lean'/(m.replace('.','/')+'.lean');assert sha(src)==q['source_sha256']
  log=Path(q['log']);log=log if log.is_absolute() else H/log
  snap=log.parent/'source.lean.txt' if cnf else H/q['source_snapshot']
  obj=H/'build-replay'/(m.replace('.','/')+'.olean')
  assert sha(log)==q['log_sha256'] and sha(snap)==q['source_sha256']
  assert sha(obj)==q['importable_object_sha256' if cnf else 'olean_sha256']
  selected.update([rp,log,snap,obj])
 for p in (H/'logs').glob('replay-attempt-*/checker.py.txt'):selected.add(p)
 for p in (H/'logs').glob('replay-*.json'):
  if read(p).get('status')=='STOPPED':selected.add(p)
 for p in (H/'logs').glob('Recovered129G.*-record.json'):
  q=read(p)
  if q['exit_code']!=0:selected.update([p,H/q['log'],H/q['source_snapshot']])
 assert {'ActualSplit129','ActualCounters129','ActualTriple129'}<={x['module'] for x in independent}
 paper=R/'paper/snake9_research.tex';editor=Path('D:/Codex/2026-10-13/new-chat/outputs/snake9_research.tex')
 assert sha(paper)==sha(editor)=='4667daec19f0b83af9fb129a263c8ae992757105414bad817c1ad13e1e11bb90'
 v=dict(status='PASS_NATIVE_PROOF_PARTIAL_LEAN_CHECKPOINT',recorded_at=datetime.datetime.now(datetime.timezone.utc).isoformat(),
  concrete_actual_semantics_checked=any(x['module']=='CoreSemantics129' for x in independent),independent_lean_receipts=independent,
  independent_axiom_reports=sum(x['reports'] for x in independent),replay_checked_modules=len(replay['checked_modules']),replay_total_modules=221,
  complete_native_replay=True,full_lean_refutation=False,actual_triple_lower_bound_proved=False,new_global_bound=False,
  endpoint122_actual_theorem_complete=True,endpoint122_audited_modules=448,endpoint122_axiom_reports=30,
  replay_snapshot_sha256=sha(observed),driver_observation=driver,scope='Candidate triple floor12 under fourth count3. Complete native replay; partial Lean refutation only.')
 (H/'data/verification.json').write_text(json.dumps(v,indent=2)+'\n',encoding='utf-8')
 c=dict(status=v['status'],goal_status='ACTIVE',previous_goal_turn='PROGRESS',base_commit='3ee421845512ff144e65dae1ee65249b771b1df6',
  verification_sha256=sha(H/'data/verification.json'),prior_checkpoint_sha256=sha(R/'milestones/128-coupled-pair/data/checkpoint.json'),
  current_interval=[191,235],interval_scope='Maintained contributor result with incomplete independent upper-proof rebuild.',
  paper_revision=126,next_paper_revision=136,paper_sha256=sha(paper),live_replay_pid=replay['pid'])
 (H/'data/checkpoint.json').write_text(json.dumps(c,indent=2)+'\n',encoding='utf-8')
 for directory in ['audit','archives','scripts','lean','build-independent','work','data']:
  for p in (H/directory).rglob('*'):
   if not p.is_file() or p in originals or '__pycache__' in p.parts or p==manifest:continue
   if p.suffix in ['.lock','.tmp'] or p.name in ['replay-progress.json','stage-paths.nul']:continue
   if directory=='data' and p.name.startswith('Recovered129G.') and p not in selected:continue
   selected.add(p)
 selected.update(p for p in H.iterdir() if p.is_file())
 selected.update(R/n for n in ['README.md','COLLABORATION.md','RESEARCH_LEDGER.md','WORKSPACE.md','milestones/README.md','handoff/README.md','handoff/CURRENT_STATUS.md','handoff/NEXT_AGENT_PROMPT.md'])
 rows=[dict(path=p.relative_to(R).as_posix(),bytes=p.stat().st_size,sha256=sha(p)) for p in sorted(selected)]
 assert all(x['bytes']<100000000 for x in rows)
 manifest.write_text(json.dumps(dict(status='SAVED_TRIPLE129_PARTIAL_LEAN_CHECKPOINT',files=rows,
  excluded_archived_originals=sorted(p.relative_to(H).as_posix() for p in originals),
  excluded_live_outputs='Running progress, unobserved receipts, active replay logs and unfinished replay objects remain local.'),indent=2)+'\n',encoding='utf-8')
j=read(manifest)
for x in j['files']:
 p=R/x['path'];assert p.stat().st_size==x['bytes'] and sha(p)==x['sha256'],x['path']
names={x['path'] for x in j['files']}|{manifest.relative_to(R).as_posix()}
g=['git','-c','core.commitGraph=false','-c','maintenance.auto=false','-c','gc.auto=0']
if '--stage' in sys.argv:
 assert not subprocess.check_output(g+['diff','--cached','--name-only'],cwd=R).strip()
 p=H/'work/stage-paths.nul';p.write_bytes(b''.join(n.encode()+b'\0' for n in sorted(names)))
 subprocess.run(g+['add','-f','--pathspec-from-file='+str(p),'--pathspec-file-nul'],cwd=R,check=True)
if '--staged' in sys.argv:
 actual=set(subprocess.check_output(g+['diff','--cached','--name-only','-z'],cwd=R).decode().strip('\0').split('\0'));assert names==actual
 p=subprocess.Popen(g+['cat-file','--batch'],cwd=R,stdin=subprocess.PIPE,stdout=subprocess.PIPE)
 for name in sorted(names):
  p.stdin.write((':'+name+'\n').encode());p.stdin.flush();header=p.stdout.readline().decode().split();assert header[1]=='blob'
  b=p.stdout.read(int(header[2]));assert p.stdout.read(1)==b'\n';expected=(R/name).read_bytes()
  if not name.startswith('milestones/129-fourth-count-three/'):expected=expected.replace(b'\r\n',b'\n')
  assert b==expected,name
 p.stdin.close();assert p.wait()==0
print(json.dumps(dict(status='PASS_STAGED' if '--staged' in sys.argv else 'PASS_SAVED',files=len(names),bytes=sum(x['bytes'] for x in j['files'])+manifest.stat().st_size,new_global_bound=False)))
