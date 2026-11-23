"""Cover all antipodal Q9 endpoint layouts, four steps inward at each end."""
import argparse
from collections import Counter
from itertools import permutations
import json
from math import perm
from pathlib import Path


def words():
    for a,b,c in permutations(range(9),3):
        yield (a,b,c,a)
    yield from permutations(range(9),4)


def positions(start, word):
    path = [start]
    for d in word:
        path.append(path[-1] ^ (1 << d))
    return path


def normalize(a,b):
    rename = {}
    return tuple(rename.setdefault(d,len(rename)) for d in a+b)


def catalogue():
    rows = {}
    for a in [(0,1,2,0),(0,1,2,3)]:
        for b in words():
            key = min(normalize(a,b), normalize(b,a))
            rows[key] = rows.get(key,0) + perm(9,len(set(a)))
    assert sum(rows.values()) == (perm(9,3)+perm(9,4))**2
    for key, weight in sorted(rows.items()):
        a,b=key[:4],key[4:]
        orbit=perm(9,len(set(key)))
        assert weight == orbit * (1 if normalize(a,b)==normalize(b,a) else 2)
        left,right=positions(0,a),positions(511,b)
        gap=min((v^w).bit_count() for v in left for w in right)
        yield dict(left=a,right=b,labeled=weight,min_distance=gap,
                   geometry="excluded" if gap<2 else "open")


def trial(a,b,budget,checker,pair18=False):
    import subprocess
    from pysat.solvers import Cadical195
    from q9_endpoint_distance_bound import build,read_path
    f,end=build(9,221,9)
    if pair18:
        from q9_free_pair_cuts import add_pair_cuts
        add_pair_cuts(f,f.nv,minimum=18)
    left,right=positions(0,a),positions(end,b)
    for v in left+right:
        f.append([v+1])
    with Cadical195(bootstrap_with=f,with_proof=True) as solver:
        solver.conf_budget(budget)
        answer=solver.solve_limited()
        result=dict(left=a,right=b,budget=budget,pair18=pair18,conflicts=solver.accum_stats()["conflicts"])
        if answer is None:
            result["status"]="UNKNOWN"
        elif answer:
            result.update(status="SAT_checked",path=read_path(solver.get_model(),9,221,end))
        else:
            stem=Path("q9_endpoint_distance_checks")/("ends_"+"".join(map(str,a))+"_"+"".join(map(str,b))+("_pair18" if pair18 else ""))
            f.to_file(str(stem)+".cnf")
            Path(str(stem)+".drat").write_text("\n".join(solver.get_proof())+"\n")
            log=subprocess.run([checker,str(stem)+".cnf",str(stem)+".drat"],capture_output=True,check=True)
            assert b"s VERIFIED" in log.stdout
            result.update(status="UNSAT_DRAT_verified",proof=str(stem)+".drat")
    return result


if __name__=="__main__":
    parser=argparse.ArgumentParser()
    parser.add_argument("--test",nargs=2)
    parser.add_argument("--checker")
    parser.add_argument("--pair18",action="store_true")
    parser.add_argument("--budget",type=int,default=5000)
    args=parser.parse_args()
    if args.test:
        a,b=(tuple(map(int,w)) for w in args.test)
        assert all(len(w)==4 and all(0<=d<9 for d in w) for w in (a,b))
        print(json.dumps(trial(a,b,args.budget,args.checker,args.pair18)))
    else:
        for row in catalogue():
            print(json.dumps(row))
