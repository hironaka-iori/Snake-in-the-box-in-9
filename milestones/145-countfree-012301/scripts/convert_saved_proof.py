"""Convert the audited historical DRAT to positive-hint LRAT without a new solve."""
from pathlib import Path
import datetime,hashlib,importlib.util,json,subprocess,time
H=Path(__file__).resolve().parents[1];R=H.parents[1];W=H/'work/conversion'
read=lambda p:json.loads(Path(p).read_text(encoding='utf-8-sig'))
def sha(p):
 d=hashlib.sha256()
 with Path(p).open('rb') as f:
  for b in iter(lambda:f.read(1048576),b''):d.update(b)
 return d.hexdigest()
def save(p,j):
 t=p.with_suffix('.tmp');t.write_text(json.dumps(j,indent=2)+'\n');t.replace(p)
loc=read(H/'data/native-locate.json');review=read(H/'data/native-review.json')
assert review['status']=='PASS_INPUT_CORE_AND_ARCHIVE_RECONSTRUCTION_NO_NEW_PROOF_REPLAY'
assert loc['review_sha256']==sha(H/'data/native-review.json')
assert loc['parameters']['directions']==[0,1,2,3,0,1] and loc['parameters']['cap']==15
for row in loc['certificate_files'].values():
 assert sha(row['original'])==row['raw_sha256'] and sha(row['archive'])==row['archive_sha256']
cnf=Path(loc['certificate_files']['cnf']['original']);drat=Path(loc['certificate_files']['drat']['original'])
exe=R/'work/share-wheels/drat-trim.exe'
utility_path=R/'milestones/109-relaxed-graph-test/upstream/milestones/10-window-aggregate/scripts/gen_lean_core.py'
def resources(pid=0):
 cmd=f"$o=Get-CimInstance Win32_OperatingSystem;$p=Get-CimInstance Win32_Process -Filter 'ProcessId={pid}'|Select-Object ProcessId,PrivatePageCount;@{{free_bytes=[long]$o.FreePhysicalMemory*1024;process=$p}}|ConvertTo-Json -Depth 3 -Compress"
 return json.loads(subprocess.check_output(['powershell','-NoProfile','-Command',cmd],text=True))
gate=resources();assert gate['free_bytes']>=3*1024**3
assert not W.exists();W.mkdir(parents=True)
record=H/'data/conversion.json';assert not record.exists()
(W/'converter.exact.py').write_bytes(Path(__file__).read_bytes())
pins={str(p.relative_to(R)):sha(p) for p in [Path(__file__),H/'data/native-locate.json',H/'data/native-review.json',cnf,drat,exe,utility_path]}
command=[str(exe),str(cnf),str(drat),'-U','-L',str(W/'raw.lrat'),'-c',str(W/'converted-core.cnf'),'-t','150']
j=dict(status='RUNNING_RUP_ONLY_CONVERSION',pid=__import__('os').getpid(),started_at=datetime.datetime.now(datetime.timezone.utc).isoformat(),
 source_files_sha256=pins,command=command,initial_resources=gate,resource_samples=[],solver_runs=0,timeout_seconds=180,variables=11378,original_clauses=92656,
 original_input_unchanged=True,lean_started=False,proof_replay_started=False)
save(record,j);start=time.monotonic();reason=None
try:
 with (W/'stdout.txt').open('xb') as out,(W/'stderr.txt').open('xb') as err:
  proc=subprocess.Popen(command,stdout=out,stderr=err);j['converter_pid']=proc.pid;save(record,j)
  while proc.poll() is None:
   q=resources(proc.pid);q['seconds']=time.monotonic()-start;j['resource_samples'].append(q);save(record,j)
   if time.monotonic()-start>180:reason='TIMEOUT'
   if q['free_bytes']<768*1024**2:reason='LOW_FREE_MEMORY'
   if q.get('process') and int(q['process']['PrivatePageCount'])>3*1024**3:reason='MEMORY_LIMIT'
   if reason:proc.kill();break
   time.sleep(3)
  code=proc.wait(timeout=30)
 j.update(conversion_exit=code,stop_reason=reason,conversion_seconds=time.monotonic()-start)
 if reason or code!=0 or b's VERIFIED' not in (W/'stdout.txt').read_bytes():
  j['status']='CONVERSION_INCOMPLETE';raise RuntimeError('No verified conversion')
 spec=importlib.util.spec_from_file_location('trim145',utility_path);utility=importlib.util.module_from_spec(spec);spec.loader.exec_module(utility)
 n,h,ids=utility.trim_lrat(str(W/'raw.lrat'),str(W/'trimmed.lrat'),92656)
 assert ids==sorted(set(ids)) and all(1<=i<=92656 for i in ids)
 save(W/'core-ids.json',ids)
 lines=cnf.read_text().splitlines();clauses=[list(map(int,l.split()[:-1])) for l in lines if l and l[0] not in 'cp']
 assert len(clauses)==92656
 (W/'core.cnf').write_text(f'p cnf 11378 {len(ids)}\n'+''.join(' '.join(map(str,clauses[i-1]))+' 0\n' for i in ids),encoding='ascii',newline='\n')
 j.update(status='PASS_RUP_ONLY_CONVERSION_DIRECT_REPLAY_PENDING',lemmas=n,hints=h,core_clauses=len(ids),core_ids_sha256=sha(W/'core-ids.json'),trimmed_sha256=sha(W/'trimmed.lrat'))
 for p,d in pins.items():assert sha(R/p)==d,p
except BaseException as e:
 j['exception']=repr(e)
 if j['status']=='RUNNING_RUP_ONLY_CONVERSION':j['status']='FAILED'
 raise
finally:
 j.update(finished_at=datetime.datetime.now(datetime.timezone.utc).isoformat(),seconds=time.monotonic()-start,
  preserved_files_sha256={p.name:sha(p) for p in W.iterdir() if p.is_file()},
  scope='RUP-only conversion of the unchanged historical DRAT. No new solver. Direct LRAT replay, Lean replay and actual-snake interpretation are separate obligations.')
 save(record,j);print(json.dumps({k:j.get(k) for k in ['status','lemmas','hints','core_clauses','seconds','stop_reason']}),flush=True)
