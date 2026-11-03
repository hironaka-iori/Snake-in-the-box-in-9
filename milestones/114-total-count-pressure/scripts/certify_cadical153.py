"""Use proof logging in the same solver family as the successful bounded probe."""
from pathlib import Path
import hashlib, json, sys, time
HERE=Path(__file__).resolve().parents[1];ROOT=HERE.parents[1]
sys.path.insert(0,str(ROOT/'work/share_packages'))
import pysat.solvers, pysolvers
from pysat.solvers import Cadical153
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
source=HERE/'work/012310-total18/full.cnf'
clauses=[]
for line in source.read_text().splitlines():
    if line.startswith('p '):
        _,_,variables,count=line.split();variables,count=int(variables),int(count)
    elif line and not line.startswith('c'):
        row=list(map(int,line.split()));assert row[-1]==0;clauses.append(row[:-1])
assert len(clauses)==count
folder=HERE/'work/012310-total18-cadical153';folder.mkdir(exist_ok=True)
record=HERE/'data/012310-total18-cadical153.json';assert not record.exists()
start=time.monotonic();calls=0
with Cadical153(bootstrap_with=clauses,with_proof=True) as solver:
    status='UNKNOWN';result=None
    while time.monotonic()-start<60:
        solver.conf_budget(1000);result=solver.solve_limited();calls+=1
        if result is not None:
            status='SAT' if result else 'UNSAT_DRAT_UNCHECKED';break
    seconds=time.monotonic()-start
    out=dict(status=status,seconds=seconds,nominal_seconds=60,calls=calls,
        clauses=count,variables=variables,cnf=source.relative_to(HERE).as_posix(),cnf_sha256=sha(source),
        source_files_sha256={str(p):sha(p) for p in [Path(pysat.solvers.__file__),Path(pysolvers.__file__)]},
        script_sha256=sha(Path(__file__)),statistics=solver.accum_stats(),
        scope='Proof-logging run on the already saved CNF including its eight valid cycle cuts. DRAT output requires independent checking and conversion before Lean use.')
    if result is False:
        proof=solver.get_proof();assert proof
        target=folder/'proof.drat';assert not target.exists()
        target.write_text('\n'.join(proof)+'\n',encoding='ascii')
        out.update(proof=target.relative_to(HERE).as_posix(),proof_lines=len(proof),proof_sha256=sha(target),proof_bytes=target.stat().st_size)
    elif result is True:
        target=folder/'model.json';target.write_text(json.dumps(solver.get_model())+'\n')
        out.update(model=target.relative_to(HERE).as_posix(),model_sha256=sha(target))
record.write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
print(json.dumps({k:out[k] for k in ['status','seconds','calls','proof_lines','proof_bytes'] if k in out}),flush=True)
