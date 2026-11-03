"""Separate Cadical153 DRAT attempt and RUP-only LRAT conversion on the exact cap17 input."""
from pathlib import Path
import datetime,hashlib,importlib.util,json,os,subprocess,sys,time
H=Path(__file__).resolve().parents[1];R=H.parents[1];W=H/'work/certificate-alternative'
RECORD=H/'data/native-alternative.json'
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
read=lambda p:json.loads(Path(p).read_text(encoding='utf-8-sig'))
def save(p,j):
 t=p.with_name(p.name+'.pending');t.write_text(json.dumps(j,indent=2)+'\n',encoding='utf-8');t.replace(p)
def load(p,n):
 s=importlib.util.spec_from_file_location(n,p);m=importlib.util.module_from_spec(s);s.loader.exec_module(m);return m
def worker():
 sys.dont_write_bytecode=True
 sys.path[:0]=[str(R/'work/share_packages'),str(R/'work/solver_packages')]
 from pysat.solvers import Cadical153
 import pysat.solvers,pysolvers
 helper=load(H/'scripts/certify_base.py','base144_worker')
 nv,clauses=helper.formula(W/'input.cnf');start=time.monotonic()
 j=dict(status='RUNNING',pid=os.getpid(),cnf_sha256=sha(W/'input.cnf'),solver='PySAT Cadical153',solver_files_sha256={str(Path(p)):sha(p) for p in [pysat.solvers.__file__,pysolvers.__file__]},variables=nv,clauses=len(clauses),extra_cycle_cuts=[])
 save(W/'worker.json',j)
 with Cadical153(bootstrap_with=clauses,with_proof=True) as solver:
  ok=None
  while ok is None and time.monotonic()-start<120:
   solver.conf_budget(10000);ok=solver.solve_limited()
  if ok is False:
   with (W/'raw.drat').open('x',encoding='ascii',newline='\n') as f:
    for line in solver.get_proof():f.write(line+'\n')
   j.update(status='UNSAT_DRAT_UNCHECKED',drat_sha256=sha(W/'raw.drat'),drat_bytes=(W/'raw.drat').stat().st_size)
  elif ok is True:
   model=solver.get_model();positive={x for x in model if x>0}
   assert all(any((x>0)==(abs(x) in positive) for x in c) for c in clauses)
   save(W/'sat-model.json',model);j.update(status='SAT_LOCAL_MODEL',model_sha256=sha(W/'sat-model.json'))
  else:j.update(status='UNKNOWN_BUDGET')
 j.update(seconds=time.monotonic()-start,cnf_unchanged=sha(W/'input.cnf')==j['cnf_sha256'])
 save(W/'worker.json',j);print(j['status'],flush=True)
def main():
 assert not W.exists() and not RECORD.exists()
 old=read(H/'data/native-base.json');assert old['status']=='TIMEOUT'
 resource=json.loads(subprocess.check_output(['powershell','-NoProfile','-Command',"$o=Get-CimInstance Win32_OperatingSystem;@{free_bytes=[long]$o.FreePhysicalMemory*1024}|ConvertTo-Json -Compress"],text=True))
 assert resource['free_bytes']>=3*1024**3
 W.mkdir(parents=True)
 source=H/'work/short/base.cnf';encoding=read(H/'data/preparation.json');assert sha(source)==encoding['cnf_sha256']
 (W/'input.cnf').write_bytes(source.read_bytes());(W/'certify.exact.py').write_bytes(Path(__file__).read_bytes())
 helper=load(H/'scripts/certify_base.py','base144_parent');nv,clauses=helper.formula(W/'input.cnf')
 trimexe=R/'work/share-wheels/drat-trim.exe';trimscript=R/'milestones/109-relaxed-graph-test/upstream/milestones/10-window-aggregate/scripts/gen_lean_core.py'
 pins={p.relative_to(R).as_posix():sha(p) for p in [Path(__file__),H/'scripts/certify_base.py',source,H/'data/preparation.json',H/'data/native-base.json',trimscript,trimexe]}
 j=dict(status='RUNNING_ALTERNATIVE_SOLVER',started_utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),pid=os.getpid(),source_files_sha256=pins,variables=nv,original_clauses=len(clauses),input_sha256=sha(W/'input.cnf'),solver_runs=1,initial_resources=resource,core_premises=dict(extra_cycle_cuts=[]),replay_hint_limit=12000000,first_attempt_status='TIMEOUT',lean_started=False)
 save(RECORD,j)
 try:
  command=[sys.executable,'-B','-X','utf8',str(Path(__file__)),'--worker']
  with (W/'worker-stdout.txt').open('xb') as out,(W/'worker-stderr.txt').open('xb') as err:
   child=subprocess.Popen(command,stdout=out,stderr=err);j.update(worker_pid=child.pid,worker_command=command);save(RECORD,j)
   try:code=child.wait(timeout=155)
   except subprocess.TimeoutExpired:
    child.kill();child.wait();j.update(status='ALTERNATIVE_TIMEOUT',worker_exit=child.returncode);return
  j['worker_exit']=code;assert code==0
  worker_record=read(W/'worker.json');j['worker_result']=worker_record
  if worker_record['status']!='UNSAT_DRAT_UNCHECKED':j['status']=worker_record['status'];return
  command=[str(trimexe),str(W/'input.cnf'),str(W/'raw.drat'),'-U','-L',str(W/'raw.lrat'),'-c',str(W/'drat-core.cnf'),'-t','120']
  j.update(status='RUNNING_RUP_ONLY_CONVERSION',conversion_command=command);save(RECORD,j)
  with (W/'conversion-stdout.txt').open('xb') as out,(W/'conversion-stderr.txt').open('xb') as err:
   child=subprocess.Popen(command,stdout=out,stderr=err);j['converter_pid']=child.pid;save(RECORD,j)
   try:code=child.wait(timeout=150)
   except subprocess.TimeoutExpired:
    child.kill();child.wait();j.update(status='CONVERSION_TIMEOUT',conversion_exit=child.returncode);return
  j['conversion_exit']=code
  assert code==0 and b's VERIFIED' in (W/'conversion-stdout.txt').read_bytes()
  utility=load(trimscript,'trim144_alternative')
  nl,nh,ids=utility.trim_lrat(str(W/'raw.lrat'),str(W/'trimmed.lrat'),len(clauses))
  assert ids==sorted(set(ids)) and all(1<=i<=len(clauses) for i in ids)
  save(W/'core-ids.json',ids)
  (W/'core.cnf').write_text(f'p cnf {nv} {len(ids)}\n'+''.join(' '.join(map(str,clauses[i-1]))+' 0\n' for i in ids),encoding='ascii',newline='\n')
  j.update(status='RUP_REPLAY_PENDING',lemmas=nl,hints=nh,core_clauses=len(ids),trim_sha256=sha(W/'trimmed.lrat'),core_sha256=sha(W/'core.cnf'),core_ids_sha256=sha(W/'core-ids.json'),raw_sha256=sha(W/'raw.lrat'),raw_bytes=(W/'raw.lrat').stat().st_size)
  save(RECORD,j)
  if nh>12000000:j['status']='NATIVE_REPLAY_PENDING_HINT_LIMIT';return
  replay=helper.replay(W/'trimmed.lrat',clauses,ids,nl,nh);save(W/'replay.json',replay)
  j.update(status='PASS_COMPLETE_NATIVE_RUP_REPLAY',replay=replay)
  for p,d in pins.items():assert sha(R/p)==d
 except BaseException as error:
  j.update(status='FAILED',error=repr(error));raise
 finally:
  j.update(finished_utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),preserved_files_sha256={p.name:sha(p) for p in W.iterdir() if p.is_file()},scope='A separate proof-producing solver attempt on the same cap17 input. Only PASS_COMPLETE_NATIVE_RUP_REPLAY establishes the independently replayed Boolean contradiction. Lean and actual-snake interpretation remain pending.')
  save(RECORD,j)
  print(json.dumps({k:v for k,v in j.items() if k not in ['source_files_sha256','preserved_files_sha256','worker_result']},indent=2),flush=True)
if __name__=='__main__':
 if '--worker' in sys.argv:worker()
 else:main()
