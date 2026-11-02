"""Alternative proof producer for exactly the saved sum21 CNF; bounded and audited."""
from pathlib import Path
import hashlib,json,subprocess,sys,time
HERE=Path(__file__).resolve().parents[1];ROOT=HERE.parents[1]
sys.path[:0]=[str(ROOT/'work/share_packages'),str(ROOT/'work/solver_packages')]
from pysat.solvers import Cadical153
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
cnf=HERE/'work/sum21/full.cnf';old=json.loads((HERE/'data/sum21-solver.json').read_text());assert sha(cnf)==old['cnf_sha256']
work=HERE/'work/sum21-c153';work.mkdir(exist_ok=True)
record=HERE/'data/sum21-c153.json';assert not record.exists()
clauses=[[int(x) for x in line.split()[:-1]] for line in cnf.read_text().splitlines() if line and not line.startswith(('c','p'))]
start=time.monotonic();calls=0;status='UNKNOWN';proof=[]
with Cadical153(bootstrap_with=clauses,with_proof=True) as solver:
    while time.monotonic()-start<60:
        solver.conf_budget(1000);result=solver.solve_limited();calls+=1
        if result is None:continue
        if result:status='SAT';break
        status='UNSAT_UNCERTIFIED';proof=solver.get_proof();break
    stats=solver.accum_stats()
out=dict(status=status,cnf_sha256=sha(cnf),calls=calls,seconds=time.monotonic()-start,solver_stats=stats,script_sha256=sha(Path(__file__)),
    scope='Fresh CaDiCaL153 proof production on the exact saved CNF. Independent verification and Lean remain separate.')
if proof:
    drat=work/'proof.drat';drat.write_bytes(('\n'.join(proof)+'\n').encode())
    out.update(drat_sha256=sha(drat),drat_bytes=drat.stat().st_size,proof_lines=len(proof))
record.write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2),flush=True)
assert status=='UNSAT_UNCERTIFIED',status
exe=ROOT/'work/share-wheels/drat-trim.exe';lrat=work/'proof.lrat';log=HERE/'logs/sum21-drat-trim.txt'
args=[str(exe),str(cnf),str(drat),'-L',str(lrat)];start=time.monotonic();verification=dict(command=args,verifier_sha256=sha(exe),timeout_seconds=60)
try:
    with log.open('w') as f:
        proc=subprocess.run(args,stdout=f,stderr=subprocess.STDOUT,timeout=60)
    verification.update(exit_code=proc.returncode,status='VERIFIED' if proc.returncode==0 and 's VERIFIED' in log.read_text() else 'FAILED',seconds=time.monotonic()-start)
except subprocess.TimeoutExpired:verification.update(status='TIMEOUT',seconds=time.monotonic()-start)
finally:
    verification['log_sha256']=sha(log)
    if lrat.exists():verification.update(lrat_sha256=sha(lrat),lrat_bytes=lrat.stat().st_size)
    (HERE/'data/sum21-drat-verification.json').write_text(json.dumps(verification,indent=2)+'\n')
print(json.dumps(verification,indent=2));assert verification['status']=='VERIFIED'
