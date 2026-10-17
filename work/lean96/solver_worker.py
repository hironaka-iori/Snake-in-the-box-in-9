"""Regenerate a missing certificate; parent supervises 300 seconds / 2048 MiB."""
from common import *
from limits import memory_limit
import argparse
def main():
    a=argparse.ArgumentParser();a.add_argument('entry',type=int);a.add_argument('attempt',type=Path);args=a.parse_args()
    memory_limit(2048)
    from pysat.solvers import Solver
    import pysat,pysolvers
    d=formula(args.entry);t=time.monotonic()
    config=dict(entry=args.entry,keep=96,total_vertices=193,solver='Glucose 4.1 (g4)',parameters='defaults; with_proof=True',
        python=sys.version,python_sat=pysat.__version__,binary_sha256=sha(pysolvers.__file__),
        encoder_sha256=sha(ROOT/'work/build_regrowth_cnf.py'),formula_sha256=sha(ROOT/f'outputs/keep96/formulas/entry{args.entry:03d}.json.gz'),
        wall_seconds=300,memory_mib=2048)
    save(args.attempt/'config.json',config)
    with Solver(name='g4',bootstrap_with=d['clauses'],with_proof=True) as s:
        sat=s.solve()
        if sat:
            model=s.get_model();values={abs(x):x>0 for x in model}
            assert all(any(values[abs(x)]==(x>0) for x in c) for c in d['clauses'])
            save(args.attempt/'model.json',model)
            result=dict(status='SAT_RELAXATION_NOT_A_SNAKE',seconds=time.monotonic()-t)
        else:
            path=args.attempt/'proof.drup.gz'
            with gzip.open(path,'wt',encoding='ascii',newline='\n') as f:
                for line in s.get_proof():f.write(line+'\n')
            result=dict(status='UNSAT',seconds=time.monotonic()-t,certificate=str(path.relative_to(ROOT)),certificate_sha256=sha(path),statistics=s.accum_stats())
        save(args.attempt/'result.json',result);print(json.dumps(result),flush=True)
if __name__=='__main__':main()
