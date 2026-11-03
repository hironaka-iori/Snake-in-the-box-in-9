"""Repeat the extracted-core proof with temporary output on the system volume."""
from pathlib import Path
import hashlib,json,shutil,subprocess,tempfile,time
HERE=Path(__file__).resolve().parents[1]
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
previous=json.loads((HERE/'data/extracted-core-solver.json').read_text())
assert previous['status']=='TIMEOUT'
source=HERE/'work/extracted-core/core.cnf';assert sha(source)==previous['core_cnf_sha256']
folder=HERE/'work/extracted-core-scratch';folder.mkdir(exist_ok=True)
record=HERE/'data/extracted-core-scratch-solver.json';assert not record.exists()
scratch=Path(tempfile.mkdtemp(prefix='snake114-core-'))
cnf=scratch/'core.cnf';raw=scratch/'core.raw.lrat';shutil.copyfile(source,cnf)
assert sha(cnf)==previous['core_cnf_sha256']
exe=Path(previous['command'][0]);assert sha(exe)==previous['solver_sha256']
command=[str(exe),'-q','--lrat','--no-binary','--seed=1',str(cnf),str(raw)]
out=dict(status='RUNNING',command=command,solver_sha256=sha(exe),script_sha256=sha(Path(__file__)),
    prior_record_sha256=sha(HERE/'data/extracted-core-solver.json'),core_cnf_sha256=sha(cnf),
    input_ids=previous['input_ids'],variables=previous['variables'],clauses=previous['clauses'],scratch=str(scratch),
    changed_condition='Same formula and solver options; proof output uses system temporary storage, then verified copy into the research folder.')
def save():record.write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
save();start=time.monotonic()
try:
    proc=subprocess.run(command,capture_output=True,timeout=60)
    stdout,stderr=proc.stdout,proc.stderr
    out.update(status='UNSAT_LRAT_UNCHECKED' if proc.returncode==20 and b's UNSATISFIABLE' in stdout else 'FAILED',exit_code=proc.returncode)
except subprocess.TimeoutExpired as e:
    stdout,stderr=e.stdout or b'',e.stderr or b'';out['status']='TIMEOUT'
out['seconds']=time.monotonic()-start
for name,rawtext in [('stdout',stdout),('stderr',stderr)]:
    path=HERE/'logs'/('extracted-core-scratch.'+name+'.log');path.write_bytes(rawtext);out[name+'_sha256']=sha(path)
if raw.exists():
    target=folder/'core.raw.lrat';assert not target.exists();shutil.copyfile(raw,target)
    assert sha(target)==sha(raw)
    out.update(raw=target.relative_to(HERE).as_posix(),raw_sha256=sha(target),raw_bytes=target.stat().st_size)
save();print(out['status'],round(out['seconds'],3),'bytes',out.get('raw_bytes'),flush=True)
