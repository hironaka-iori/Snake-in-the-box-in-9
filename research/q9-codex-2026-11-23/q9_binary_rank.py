"""Exact induced-path SAT with a shared binary increment at each vertex."""
import argparse
import json
import subprocess
from pathlib import Path

from pysat.formula import IDPool
from pysat.solvers import Cadical195

from q9_endpoint_distance_bound import build, read_path
from q9_free_pair_cuts import add_pair_cuts


def binary_formula(dim, length, distance, pair17=False, lex=False, population=False, interfaces=False):
    f, end = build(dim, length, distance, include_rank=False)
    n = 1 << dim
    height = (length - distance) // 2
    width = max(1, height.bit_length())
    pool = IDPool(start_from=f.nv+1)
    rank = [[pool.id() for _ in range(width)] for v in range(n)]
    increment = []
    overflow = []
    for v, bits in enumerate(rank):
        bumped = [-bits[0]]
        carry = bits[0]
        for bit in bits[1:]:
            total, following = pool.id(), pool.id()
            f.extend([[-carry,-bit,-total], [carry,bit,-total],
                      [carry,-bit,total], [-carry,bit,total],
                      [-following,carry], [-following,bit], [-carry,-bit,following]])
            bumped.append(total)
            carry = following
        increment.append(bumped)
        overflow.append(carry)
        if v in (0,end):
            value = height if v == end else 0
            for index, bit in enumerate(bits):
                f.append([bit if value >> index & 1 else -bit])
    for low in range(n):
        for d in range(dim):
            high = low | (1 << d)
            if high == low:
                continue
            use_increment = pool.id()
            edge = [-low-1,-high-1]
            f.append([*edge,-use_increment,-overflow[high]])
            for target, same, bumped in zip(rank[low],rank[high],increment[high]):
                f.extend([[*edge,use_increment,-target,same],
                          [*edge,use_increment,target,-same],
                          [*edge,-use_increment,-target,bumped],
                          [*edge,-use_increment,target,-bumped]])
    if pair17:
        assert (dim,length) == (9,221)
        add_pair_cuts(f,f.nv,minimum=17)
    if lex:
        from q9_endpoint_lex import add_endpoint_lex
        add_endpoint_lex(f,dim,distance)
    if population or interfaces:
        assert (dim,length,pair17) == (9,221,True)
        from q9_projection_population import add_population_cut
        for i,j in ((0,1),(2,3),(4,5),(6,7)):
            add_population_cut(f,i,j,interfaces=interfaces)
    return f,end


def main():
    parser = argparse.ArgumentParser()
    for name in ("dim","length","distance","budget"):
        parser.add_argument(name,type=int)
    parser.add_argument("--pair17",action="store_true")
    parser.add_argument("--lex", action="store_true")
    parser.add_argument("--proof",nargs=2,metavar=("FILE_STEM","CHECKER"))
    parser.add_argument("--population",action="store_true")
    parser.add_argument("--interfaces",action="store_true")
    args = parser.parse_args()
    f,end = binary_formula(args.dim,args.length,args.distance,args.pair17,args.lex,args.population,args.interfaces)
    data = dict(dimension=args.dim,length=args.length,distance=args.distance,
                variables=f.nv,clauses=len(f.clauses),pair17=args.pair17,lex=args.lex,population=args.population,interfaces=args.interfaces)
    print(json.dumps(dict(status="STARTED",**data)),flush=True)
    with Cadical195(bootstrap_with=f,with_proof=bool(args.proof)) as solver:
        solver.conf_budget(args.budget)
        answer = solver.solve_limited()
        if answer is None:
            data["status"]="UNKNOWN"
        elif answer:
            data.update(status="SAT_checked",path=read_path(solver.get_model(),args.dim,args.length,end))
        elif args.proof:
            stem,checker=args.proof
            cnf,trace=Path(stem+".cnf"),Path(stem+".drat")
            f.to_file(str(cnf))
            trace.write_text("\n".join(solver.get_proof())+"\n")
            check=subprocess.run([checker,str(cnf),str(trace)],capture_output=True,check=True)
            assert b"s VERIFIED" in check.stdout
            data.update(status="UNSAT_DRAT_verified",trace=str(trace))
        else:
            data["status"]="UNSAT_solver"
        print(json.dumps(dict(data,**solver.accum_stats())),flush=True)


if __name__=="__main__":
    main()
