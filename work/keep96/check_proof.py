"""Executable DRUP/RUP replay with Glucose3 unit propagation; NOT Lean verification.

Deletion lines may be ignored: all retained clauses have already been justified.
Non-RUP additions are rejected rather than silently treated as RAT steps.
"""
import argparse
import time
from common import *
from worker import memory_limit


def replay(clauses, proof):
    from pysat.solvers import Solver
    additions=deletions=0
    with Solver(name='g3',bootstrap_with=clauses) as solver:
        ended=False
        for lineno,line in enumerate(proof,1):
            fields=line.split()
            if not fields:continue
            if fields[0]=='d':deletions+=1;continue
            values=list(map(int,fields))
            if values[-1]!=0 or 0 in values[:-1]:raise ValueError('malformed proof')
            clause=values[:-1]
            consistent,_=solver.propagate(assumptions=[-lit for lit in clause])
            if consistent:raise ValueError(f'non-RUP addition at line {lineno}')
            solver.add_clause(clause);additions+=1
            if not clause:ended=True
        if not ended:
            consistent,_=solver.propagate()
            if consistent:raise ValueError('no empty clause and no root unit contradiction')
    return dict(status='PASSED_EXECUTABLE_RUP_CHECK',additions=additions,ignored_deletions=deletions)


def main():
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('attempt',type=Path)
    ap.add_argument('--memory-mib',type=int,default=2048);a=ap.parse_args()
    memory_limit(a.memory_mib)
    result=json.loads((a.attempt/'result.json').read_text())
    if result['status']!='UNSAT':raise ValueError('not an UNSAT record')
    formula=next(ROOT/p for p in result['identity']['formula_hashes'] if p.endswith('.json.gz'))
    certificate=ROOT/result['certificate']
    for p in (formula,certificate):
        if sha(p)!=result['artifact_hashes'][p.relative_to(ROOT).as_posix()]:raise ValueError('artifact hash mismatch')
    data=json.loads(gzip.decompress(formula.read_bytes()));start=time.perf_counter()
    with gzip.open(certificate,'rt') as f:r=replay(data['clauses'],f)
    r.update(seconds=time.perf_counter()-start,formula_sha256=sha(formula),certificate_sha256=sha(certificate),
             checker_sha256=sha(Path(__file__)),scope='Executable unit-propagation check only; no Lean formalization')
    save(a.attempt/'drup-check.json',r);print(json.dumps(r),flush=True)


if __name__=='__main__':main()
