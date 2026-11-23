"""Produce DRAT for a geometry obstruction on overlapping direction windows."""
import argparse
from itertools import combinations
import json
from pathlib import Path
import subprocess

from pysat.card import CardEnc, EncType
from pysat.formula import CNF, IDPool
from pysat.solvers import Cadical195


def formula(windows):
    n=len(windows)+8
    pool=IDPool()
    f=CNF()
    dirs=[[pool.id() for _ in range(9)] for _ in range(n)]
    coords=[[pool.id() for _ in range(9)] for _ in range(n+1)]
    f.extend([-v] for v in coords[0])
    for k,row in enumerate(dirs):
        f.extend(CardEnc.equals(row,1,vpool=pool,encoding=EncType.pairwise).clauses)
        for d,direction in enumerate(row):
            a,b=coords[k][d],coords[k+1][d]
            f.extend([[-direction,-a,-b],[-direction,a,b],
                      [direction,-a,b],[direction,a,-b]])
    for start,patterns in enumerate(windows):
        selectors=[pool.id() for _ in patterns]
        f.append(selectors)
        for selector,pattern in zip(selectors,patterns):
            if start==0:
                f.extend([-selector,dirs[j][d]] for j,d in enumerate(pattern))
                continue
            for i,j in combinations(range(9),2):
                for a,b in zip(dirs[start+i],dirs[start+j]):
                    if pattern[i]==pattern[j]:
                        f.extend([[-selector,-a,b],[-selector,a,-b]])
                    else:
                        f.append([-selector,-a,-b])
    for i in range(n+1):
        for j in range(i+2,n+1):
            differences=[]
            for a,b in zip(coords[i],coords[j]):
                x=pool.id()
                f.extend([[-a,-b,-x],[a,b,-x],[-a,b,x],[a,-b,x]])
                differences.append(x)
            f.extend(CardEnc.atleast(differences,2,vpool=pool,encoding=EncType.seqcounter).clauses)
    return f


def run(windows,out,checker):
    for part,tag in ((windows[:-1],"left"),(windows[1:],"right"),(windows,"full")):
        f=formula(part)
        with Cadical195(bootstrap_with=f,with_proof=True) as sat:
            result=sat.solve()
            assert result==(tag!="full")
            if not result:
                cnf=out/"q9_window11_geometry.cnf"
                drat=out/"q9_window11_geometry.drat"
                f.to_file(str(cnf))
                drat.write_text("\n".join(sat.get_proof())+"\n")
                check=subprocess.run([checker,str(cnf),str(drat)],check=True,capture_output=True)
                assert b"s VERIFIED" in check.stdout
            print(json.dumps(dict(tag=tag,status="SAT" if result else "UNSAT_DRAT_verified",
                                  steps=len(part)+8,conflicts=sat.accum_stats()["conflicts"])))


if __name__=="__main__":
    p=argparse.ArgumentParser()
    p.add_argument("report",type=Path)
    p.add_argument("out",type=Path)
    p.add_argument("checker")
    a=p.parse_args()
    for line in a.report.read_text().splitlines():
        row=json.loads(line)
        if row["impossible"]:
            run(row["impossible"][0]["words"],a.out,a.checker)
            break
