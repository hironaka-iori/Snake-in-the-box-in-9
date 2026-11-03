"""Run a bounded search on the derived-clause augmentation; preserve every outcome."""
from pathlib import Path
import datetime,hashlib,json,os,subprocess,sys,time
H=Path(__file__).resolve().parents[1];R=H.parents[1]
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
read=lambda p:json.loads(p.read_text(encoding='utf-8-sig'))
p=read(H/'data/prelude.json');cnf=H/'work/augmented.cnf'
assert sha(cnf)==p['augmented_sha256']
exe=Path('D:/Codex/2026-10-01/it-should-have-a-property-of/work/lean-research/lean-4.19.0-windows/bin/cadical.exe')
raw=H/'work/augmented.raw.lrat';outpath=H/'data/search.json';stdout=H/'logs/search.stdout.txt';stderr=H/'logs/search.stderr.txt'
assert not outpath.exists() and not raw.exists()
command=[str(exe),'-q','--lrat','--no-binary','--seed=1',str(cnf),str(raw)]
out=dict(status='RUNNING',pid=os.getpid(),command=command,solver_sha256=sha(exe),cnf_sha256=sha(cnf),prelude_sha256=p['prelude_sha256'],script_sha256=sha(Path(__file__)),started_at=datetime.datetime.now(datetime.timezone.utc).isoformat(),timeout_seconds=180)
def save():outpath.write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
save();start=time.monotonic()
with stdout.open('wb') as so,stderr.open('wb') as se:
 proc=subprocess.Popen(command,stdout=so,stderr=se);out['solver_pid']=proc.pid;save()
 try:
  code=proc.wait(timeout=180);text=stdout.read_text(errors='replace')
  out.update(exit_code=code,status='NATIVE_UNSAT_PENDING_ORIGINAL_REPLAY' if code==20 and 's UNSATISFIABLE' in text else 'NATIVE_SAT' if code==10 and 's SATISFIABLE' in text else 'FAILED')
 except subprocess.TimeoutExpired:
  proc.kill();proc.wait(timeout=15);out.update(exit_code=proc.returncode,status='TIMEOUT')
out.update(seconds=time.monotonic()-start,stdout_sha256=sha(stdout),stderr_sha256=sha(stderr),raw_sha256=sha(raw),raw_bytes=raw.stat().st_size)
save()
if out['status']=='NATIVE_SAT':
 sys.dont_write_bytecode=True
 sys.path[:0]=[str(R/'milestones/28-direct-share-certificates/scripts'),str(R/'milestones/10-window-aggregate/scripts'),str(R/'work/solver_packages')]
 from direct import census
 vals=[int(v) for line in stdout.read_text().splitlines() if line.startswith('v ') for v in line.split()[1:] if v!='0'];assigned=set(vals)
 assert len(vals)==len(set(map(abs,vals)))==p['original_variables']
 for line in cnf.read_text().splitlines()[1:]:
  c=list(map(int,line.split()));assert c[-1]==0 and any(x in assigned for x in c[:-1])
 case=read(R/'milestones/125-critical-six-count/data/probes/0120324-total22-positive.json')
 selected={v for v in range(512) if v+1 in assigned};c=census(selected,9,case['window'][1:-1]);c.pop('degree')
 assert sum(c['alpha'])<=22 and all(lo<=a<=hi for a,(lo,hi) in zip(c['alpha'],case['bounds']))
 out.update(status='NATIVE_CYCLIC_MODEL' if c['cycles'] else 'FULL_PATH_CANDIDATE',selected=sorted(selected),census=c)
 save()
if out['status']=='NATIVE_UNSAT_PENDING_ORIGINAL_REPLAY':
 combined=H/'work/combined.raw.lrat';assert not combined.exists()
 with combined.open('wb') as dest:
  for src in [H/'work/prelude.lrat',raw]:
   with src.open('rb') as stream:
    for block in iter(lambda:stream.read(1024*1024),b''):dest.write(block)
 out.update(combined_sha256=sha(combined),combined_bytes=combined.stat().st_size,replay_input_clauses=p['original_clauses'])
 save()
out['scope']='A bounded changed-encoding search. Any UNSAT result requires combined proof replay against original106348 clauses and a complete Lean interpretation/refutation. Timeout is inconclusive.'
save();print(json.dumps(out,indent=2),flush=True)
