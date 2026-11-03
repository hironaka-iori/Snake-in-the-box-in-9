"""Bounded reuse of the existing compact-core LRAT workflow; preserve old evidence."""
from pathlib import Path
import datetime,hashlib,importlib.util,json,subprocess,time
H=Path(__file__).resolve().parents[1];R=H.parents[1];W=H/'work/compact'
read=lambda p:json.loads(Path(p).read_text(encoding='utf-8-sig'))
def sha(p):
 d=hashlib.sha256()
 with Path(p).open('rb') as f:
  for b in iter(lambda:f.read(1048576),b''):d.update(b)
 return d.hexdigest()
def save(p,j):
 t=p.with_suffix('.tmp');t.write_text(json.dumps(j,indent=2)+'\n');t.replace(p)
loc=read(H/'data/native-locate.json');row=loc['certificate_files']['core.cnf'];source=Path(row['original'])
assert sha(source)==row['raw_sha256']
assert read(H/'data/native-review.json')['status']=='PASS_INPUT_CORE_AND_ARCHIVE_RECONSTRUCTION_NO_NEW_PROOF_REPLAY'
exe=Path('D:/Codex/2026-10-01/it-should-have-a-property-of/work/lean-research/lean-4.19.0-windows/bin/cadical.exe')
assert sha(exe)=='4fb5f4f94a3632c185ea763f7da627d40038cca38d9481952d00d04cc881c94f'
resource=json.loads(subprocess.check_output(['powershell','-NoProfile','-Command',"$o=Get-CimInstance Win32_OperatingSystem;@{free_bytes=[long]$o.FreePhysicalMemory*1024}|ConvertTo-Json -Compress"],text=True))
assert resource['free_bytes']>=3*1024**3
assert not W.exists();W.mkdir(parents=True);(W/'input.cnf').write_bytes(source.read_bytes())
record=H/'data/compact-certificate.json';assert not record.exists();start=time.monotonic()
command=[str(exe),'-q','--lrat','--no-binary',str(W/'input.cnf'),str(W/'raw.lrat')]
utility_path=R/'milestones/109-relaxed-graph-test/upstream/milestones/10-window-aggregate/scripts/gen_lean_core.py'
pins={str(p):sha(p) for p in [Path(__file__),H/'data/native-locate.json',H/'data/native-review.json',source,exe,utility_path]}
j=dict(status='RUNNING_BOUNDED_COMPACT_CORE_SOLVE',pid=__import__('os').getpid(),started_at=datetime.datetime.now(datetime.timezone.utc).isoformat(),
 command=command,solver_timeout_seconds=90,variables=11378,input_clauses=12977,source_files_sha256=pins,resource_gate=resource,
 scope='The unchanged original core is a subset of the full input. This is a new bounded proof-size experiment; no local theorem is claimed.')
save(record,j)
try:
 with (W/'stdout.txt').open('xb') as out,(W/'stderr.txt').open('xb') as err:
  proc=subprocess.Popen(command,stdout=out,stderr=err);j['solver_pid']=proc.pid;save(record,j)
  try:code=proc.wait(timeout=90)
  except subprocess.TimeoutExpired:
   proc.kill();proc.wait();j.update(status='TIMEOUT',solver_exit=proc.returncode);raise TimeoutError('Compact-core90secondlimit')
 j['solver_exit']=code
 if code==10:j['status']='SAT_REQUIRES_INVESTIGATION';raise RuntimeError('Unexpected SAT on saved core')
 assert code==20 and b's UNSATISFIABLE' in (W/'stdout.txt').read_bytes()
 spec=importlib.util.spec_from_file_location('trimcompact145',utility_path);m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m)
 n,h,ids=m.trim_lrat(str(W/'raw.lrat'),str(W/'trimmed.lrat'),12977)
 assert ids==sorted(set(ids)) and all(1<=i<=12977 for i in ids)
 save(W/'core-ids.json',ids)
 j.update(status='COMPACT_UNSAT_LRAT_GENERATED_REPLAY_PENDING',lemmas=n,hints=h,retained_core_clauses=len(ids),trimmed_sha256=sha(W/'trimmed.lrat'))
 for p,d in pins.items():assert sha(p)==d,p
except BaseException as e:
 j['exception']=repr(e)
 if j['status']=='RUNNING_BOUNDED_COMPACT_CORE_SOLVE':j['status']='FAILED'
 raise
finally:
 j.update(seconds=time.monotonic()-start,finished_at=datetime.datetime.now(datetime.timezone.utc).isoformat(),preserved_files_sha256={p.name:sha(p) for p in W.iterdir() if p.is_file()})
 save(record,j);print(json.dumps({k:j.get(k) for k in ['status','lemmas','hints','retained_core_clauses','seconds']}),flush=True)
