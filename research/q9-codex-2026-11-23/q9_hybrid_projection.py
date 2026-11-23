"""Bind the verified low-frequency projection cuts to actual Q9 vertices and edges."""
import argparse
import hashlib
import json
from pathlib import Path
import subprocess

from pysat.card import CardEnc, EncType
from pysat.formula import IDPool
from pysat.solvers import Cadical195

from q9_endpoint_distance_bound import read_path
from q9_modular_orientation import modular
from q9_three_axis_profiles import formula as projected_formula


def build(counts,distance,exact_cuts,star_cuts):
    assert tuple(sorted(counts))==tuple(counts) and sum(counts)<=29
    projected_end=sum((n%2)<<i for i,n in enumerate(counts))
    assert 0<=distance-projected_end.bit_count()<=6
    axes=[i for i,n in enumerate(counts) if n%2]+list(range(3,3+distance-projected_end.bit_count()))
    # The original model normalizes the terminal to the lowest distance bits.
    # Remap the projection axes accordingly, leaving selection variables in original numbering.
    axes += [i for i in range(9) if i not in axes]
    real_position={axis:i for i,axis in enumerate(axes)}
    def cube_vertex(v):
        return sum((1<<real_position[i]) for i in range(9) if v>>i&1)
    f,end=modular(9,221,distance,7,pair17=True)
    abstract,edges,components,crossings=projected_formula(counts,projected_end,exact_cuts,star_cuts)
    offset=f.nv
    def shifted(literal):
        return offset+literal if literal>0 else literal-offset
    f.extend([shifted(x) for x in clause] for clause in abstract.clauses)
    pool=IDPool(start_from=f.nv+1)
    def bind(lits,thresholds):
        f.extend(CardEnc.equals(lits+[-shifted(x) for x in thresholds],
                                len(thresholds),vpool=pool,encoding=EncType.cardnetwrk).clauses)
    for face in range(8):
        bind([cube_vertex(face|8*v)+1 for v in range(64)],edges[face]+components[face])
    for (a,b),thresholds in crossings.items():
        bonds=[]
        for c in range(64):
            u,v=cube_vertex(a|8*c)+1,cube_vertex(b|8*c)+1
            x=pool.id()
            f.extend([[-x,u],[-x,v],[x,-u,-v]])
            bonds.append(x)
        bind(bonds,thresholds)
    return f,end


def run(args):
    exact=json.loads(args.exact_cuts.read_text())
    stars=[row for file in args.star_cuts for row in json.loads(file.read_text())]
    f,end=build(args.counts,args.distance,exact,stars)
    summary=dict(counts=args.counts,distance=args.distance,exact_cuts=len(exact),star_cuts=len(stars),
                 variables=f.nv,clauses=len(f.clauses),budget=args.budget,
                 cut_sources={str(p):hashlib.sha256(p.read_bytes()).hexdigest()
                              for p in [args.exact_cuts,*args.star_cuts]})
    print(json.dumps(dict(summary,status="STARTED")),flush=True)
    with Cadical195(bootstrap_with=f,with_proof=True) as sat:
        sat.conf_budget(args.budget)
        result=sat.solve_limited()
        if result is None:
            summary.update(status="UNKNOWN")
        elif result:
            summary.update(status="SAT_checked",path=read_path(sat.get_model(),9,221,end))
        else:
            cnf,proof=args.output.with_suffix(".cnf"),args.output.with_suffix(".drat")
            f.to_file(str(cnf))
            proof.write_text("\n".join(sat.get_proof())+"\n")
            r=subprocess.run([args.checker,str(cnf),str(proof)],check=True,capture_output=True)
            assert b"s VERIFIED" in r.stdout
            summary.update(status="UNSAT_DRAT_verified",proof=str(proof))
        print(json.dumps(dict(summary,**sat.accum_stats())),flush=True)


if __name__=="__main__":
    parser=argparse.ArgumentParser()
    parser.add_argument("distance",type=int)
    parser.add_argument("counts",type=int,nargs=3)
    parser.add_argument("output",type=Path)
    parser.add_argument("checker")
    parser.add_argument("--exact-cuts",type=Path,required=True)
    parser.add_argument("--star-cuts",type=Path,nargs="+",default=[])
    parser.add_argument("--budget",type=int,default=400000)
    run(parser.parse_args())
