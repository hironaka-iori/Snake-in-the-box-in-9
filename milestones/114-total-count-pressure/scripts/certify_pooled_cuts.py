"""Produce a proof for the validated cycle-cut strengthening using temporary I/O."""
from pathlib import Path
import hashlib,json,shutil,subprocess,tempfile,time
HERE=Path(__file__).resolve().parents[1]
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
spec=HERE/'data/cycle-cut-pool-extended.json';data=json.loads(spec.read_text())
source=HERE/data['cnf'];assert sha(source)==data['cnf_sha256']
record=HERE/'data/pooled-cuts-solver.json';assert not record.exists()
scratch=Path(tempfile.mkdtemp(prefix='snake114-pooled-'));cnf=scratch/'full.cnf';raw=scratch/'full.raw.lrat'
shutil.copyfile(source,cnf);assert sha(cnf)==data['cnf_sha256']
exe=Path('D:/Codex/2026-10-01/it-should-have-a-property-of/work/lean-research/lean-4.19.0-windows/bin/cadical.exe')
command=[str(exe),'-q','--lrat','--no-binary','--seed=1',str(cnf),str(raw)]
out=dict(status='RUNNING',command=command,solver_sha256=sha(exe),script_sha256=sha(Path(__file__)),
    specification_sha256=sha(spec),cnf_sha256=sha(cnf),clauses=data['clauses'],variables=data['variables'],
    scratch=str(scratch),cycle_cuts=len(data['cuts']),timeout_seconds=60)
def save():record.write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
save();start=time.monotonic()
try:
    proc=subprocess.run(command,capture_output=True,timeout=60);stdout,stderr=proc.stdout,proc.stderr
    out.update(status='UNSAT_LRAT_UNCHECKED' if proc.returncode==20 and b's UNSATISFIABLE' in stdout else 'FAILED',exit_code=proc.returncode)
except subprocess.TimeoutExpired as e:
    stdout,stderr=e.stdout or b'',e.stderr or b'';out['status']='TIMEOUT'
out['seconds']=time.monotonic()-start
for name,rawtext in [('stdout',stdout),('stderr',stderr)]:
    path=HERE/'logs'/('pooled-cuts.'+name+'.log');path.write_bytes(rawtext);out[name+'_sha256']=sha(path)
if raw.exists():
    target=source.with_name('full.raw.lrat');assert not target.exists();shutil.copyfile(raw,target)
    assert sha(target)==sha(raw)
    out.update(raw=target.relative_to(HERE).as_posix(),raw_sha256=sha(target),raw_bytes=target.stat().st_size)
save();print(out['status'],round(out['seconds'],3),'bytes',out.get('raw_bytes'),flush=True)
