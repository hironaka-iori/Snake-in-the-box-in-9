"""A separate count-free012034 cap12 input, preserving every older share20 artifact."""
from pathlib import Path
import datetime,gzip,hashlib,json,os,subprocess,sys,time
H=Path(__file__).resolve().parents[1];R=H.parents[1]
for d in ['data','audit','work/short','scripts']:(H/d).mkdir(parents=True,exist_ok=True)
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
read=lambda p:json.loads(Path(p).read_text(encoding='utf-8-sig'))
def save(p,j):p.write_text(json.dumps(j,indent=2)+'\n',encoding='utf-8')
assert not (H/'work/short/base.cnf').exists()
g=['git','-c','core.commitGraph=false','-c','maintenance.auto=false','-c','gc.auto=0']
r=subprocess.run(g+['fetch','origin'],cwd=R,capture_output=True,text=True,check=True)
out=lambda a:subprocess.check_output(g+a,cwd=R,text=True).strip()
head=out(['rev-parse','HEAD']);remote=out(['rev-parse','origin/main'])
assert head==remote=='d29e9db3e5590942fbd4ba4a966e89b1f65870ab'
save(H/'data/repository-check.json',dict(recorded_at=datetime.datetime.now(datetime.timezone.utc).isoformat(),head=head,origin_main=remote,fetch_exit_code=r.returncode,fetch_stdout=r.stdout,fetch_stderr=r.stderr,remote_tips=out(['for-each-ref','--format=%(refname) %(objectname)','refs/remotes/origin'])))
resources=json.loads(subprocess.check_output(['powershell','-NoProfile','-Command',
 "$o=Get-CimInstance Win32_OperatingSystem;$p=@(Get-CimInstance Win32_Process | Where-Object {$_.Name -in @('python.exe','lean.exe','cadical.exe')} | Select-Object ProcessId,Name,CommandLine);@{free_bytes=[long]$o.FreePhysicalMemory*1024;processes=$p}|ConvertTo-Json -Depth 4 -Compress"],text=True))
assert resources['free_bytes']>=1610612736
assert not any('case7302' in (p.get('CommandLine') or '') for p in resources['processes'])
prior=R/'milestones/73-countfree-share-catalogue/cases/case7302/logs/completion-record.json'
priorbytes=prior.read_bytes();(H/'audit/old-share20-completion-record.json').write_bytes(priorbytes)
rows=read(prior)['records'];last=rows[-1]
save(H/'data/old-share20-observation.json',dict(recorded_at=datetime.datetime.now(datetime.timezone.utc).isoformat(),resources=resources,source=str(prior),source_sha256=sha(prior),snapshot='audit/old-share20-completion-record.json',last_record=last,no_live_case7302_driver=True,scope='Read-only snapshot; no older input, proof source or object is changed.'))
sys.dont_write_bytecode=True
sys.path.insert(0,str(R/'milestones/28-direct-share-certificates/scripts'))
from tagged_share import TaggedShare
import gen_lean_sat,wincert,tagged_share
sources=[Path(__file__),Path(tagged_share.__file__),Path(gen_lean_sat.__file__),Path(wincert.__file__),R/'milestones/142-retuned-occurrence-credit/data/share-targets.json']
pins={p.relative_to(R).as_posix():sha(p) for p in sources}
start=time.monotonic();e=TaggedShare([0,1,2,0,3,4],[(0,21)]*5,12)
cnf=H/'work/short/base.cnf'
with cnf.open('w',encoding='ascii',newline='\n') as f:
 f.write(f'p cnf {e.nv} {len(e.clauses)}\n')
 for c in e.clauses:f.write(' '.join(map(str,c))+' 0\n')
with gzip.open(H/'work/short/meanings.json.gz','wt',encoding='utf-8') as f:
 json.dump(dict(meaning=e.meaning,smeaning=e.smeaning,ctrs=e.ctrs,tots=e.tots,tags=e.tags),f)
for p in sources:
 if p.suffix=='.py':(H/'audit'/('input-source-'+p.name+'.txt')).write_bytes(p.read_bytes())
j=dict(status='PREPARED_UNSOLVED_LOCAL_SHARE_QUERY',directions=[0,1,2,0,3,4],bounds=[[0,21]]*5,share_cap=12,target_share=13,resolution=12,radius=4,extra_cycle_cuts=[],window=e.window,variables=e.nv,clauses=len(e.clauses),cnf_sha256=sha(cnf),meanings_sha256=sha(H/'work/short/meanings.json.gz'),source_files_sha256=pins,seconds=time.monotonic()-start,scope='Count-free local contradiction query only. No solver result, Lean theorem or actual-snake conclusion is asserted.')
save(H/'work/short/encoding.json',j);save(H/'data/preparation.json',j)
print(json.dumps({k:v for k,v in j.items() if k!='source_files_sha256'}))
