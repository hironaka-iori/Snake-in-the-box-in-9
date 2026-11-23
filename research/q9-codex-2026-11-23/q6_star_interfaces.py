"""Test simultaneous interfaces around one dense Q6 face."""
import argparse
from collections import Counter
import gzip
from itertools import combinations, product
import json
from pathlib import Path
import signal
import subprocess
import tempfile

from pysat.card import CardEnc, EncType
from pysat.formula import CNF, IDPool
from pysat.solvers import Cadical195

from q6_exact_anchored_profiles import catalogue
from verify_q9_free_dimension_cuts import deg


def stars(path):
    frequencies=Counter()
    for line in path.read_text().splitlines():
        row=json.loads(line)
        if row["status"]!="FEASIBLE_RELAXATION":
            continue
        faces=list(zip(row["edges"],row["components"]))
        neighbors=[[] for _ in range(8)]
        interfaces=[(a,a^(1<<i)) for i in range(3) for a in range(8) if not a>>i&1]
        for (a,b),r in zip(interfaces,row["crossings"]):
            if r:
                neighbors[a].append((*faces[b],r))
                neighbors[b].append((*faces[a],r))
        for v,(e,c) in enumerate(faces):
            if e in (25,26) and len(neighbors[v])>=2:
                frequencies[(e,c,tuple(sorted(neighbors[v],reverse=True)))]+=1
    return sorted(frequencies,key=lambda k:(-k[0],-frequencies[k],-len(k[2]),k))


def formula(anchor, leaves):
    points={v for v in range(64) if anchor>>v&1}
    ports={v:2-deg(points,v,6) for v in points if deg(points,v,6)<2}
    allowed=set(range(64))-(points-ports.keys())
    f=CNF()
    pool=IDPool(start_from=1+64*len(leaves))
    def count(lits,n,encoder):
        if n>len(lits):
            f.append([])
        else:
            f.extend(encoder(lits,n,vpool=pool,encoding=EncType.cardnetwrk).clauses)
    for side,(e,c,r) in enumerate(leaves):
        base=1+64*side
        bonds=[]
        for v in sorted(allowed):
            adj=sorted({v^(1<<i) for i in range(6)}&allowed)
            for bad in combinations(adj,2 if v in ports else 3):
                f.append([-base-v,*(-base-w for w in bad)])
            for w in adj:
                if v<w:
                    edge=pool.id()
                    f.extend([[-edge,base+v],[-edge,base+w],[edge,-base-v,-base-w]])
                    bonds.append(edge)
            for a,b in combinations(range(6),2):
                x,y=1<<a,1<<b
                sq={v,v^x,v^y,v^x^y}
                if not v&(x|y) and sq<=allowed:
                    f.append([-base-w for w in sorted(sq)])
        if c is not None:
            count([base+v for v in sorted(allowed)],e+c,CardEnc.equals)
        encoder=CardEnc.atleast if c is None else CardEnc.equals
        count(bonds,e,encoder)
        count([base+v for v in sorted(ports)],r,encoder)
    for v,capacity in sorted(ports.items()):
        for choices in combinations(range(len(leaves)),capacity+1):
            f.append([-1-64*side-v for side in choices])
    return f


def check(f, proof, checker):
    if [] in f.clauses:
        # An explicit empty input clause certifies UNSAT directly. This
        # version of drat-trim prints VERIFIED but exits 1 on such inputs.
        return
    with tempfile.TemporaryDirectory() as tmp:
        cnf,trace=Path(tmp)/"star.cnf",Path(tmp)/"star.drat"
        f.to_file(str(cnf))
        trace.write_text(proof)
        command = [checker,str(cnf),str(trace)]
        r = subprocess.run(command,capture_output=True)
        if r.returncode == -signal.SIGBUS:
            r = subprocess.run(command,capture_output=True)
        r.check_returncode()
        assert b"s VERIFIED" in r.stdout.splitlines()


def search(key, anchors, checker, budget):
    cases=[]
    for anchor in anchors:
        f=formula(anchor,key[2])
        with Cadical195(bootstrap_with=f,with_proof=True) as sat:
            sat.conf_budget(budget)
            answer=sat.solve_limited()
            if answer is None:
                cases.append(dict(anchor=f"{anchor:016x}",status="UNKNOWN"))
            elif answer:
                return dict(key=key,status="FEASIBLE_RELAXATION",
                            anchor=f"{anchor:016x}",tested=len(cases)+1)
            else:
                proof="\n".join(sat.get_proof())+"\n"
                check(f,proof,checker)
                cases.append(dict(anchor=f"{anchor:016x}",status="UNSAT_DRAT_verified",proof=proof))
    status="UNSAT_all_anchors_verified" if all(r["status"]=="UNSAT_DRAT_verified" for r in cases) else "UNKNOWN"
    return dict(key=key,status=status,cases=cases)


if __name__=="__main__":
    parser=argparse.ArgumentParser()
    parser.add_argument("profiles",type=Path)
    parser.add_argument("out",type=Path)
    parser.add_argument("checker")
    parser.add_argument("--limit",type=int,default=20)
    parser.add_argument("--budget",type=int,default=6000)
    parser.add_argument("--generalize", action="store_true")
    a=parser.parse_args()
    if a.generalize:
        keys=[(e,c,tuple((target,None,r) for target,_,r in leaves))
              for e,c,leaves in json.loads(a.profiles.read_text())]
        keys=list(dict.fromkeys(keys))
    else:
        keys=stars(a.profiles)
    filename="q6_general_star_interfaces.jsonl.gz" if a.generalize else "q6_star_interfaces.jsonl.gz"
    with gzip.open(a.out/filename,"wt") as archive:
        for key in keys[:a.limit]:
            e,c,_=key
            suffix="catalogue.log" if e==25 else "interfaces.log"
            anchors=list(catalogue(a.out/f"q6_{e}_edge_{suffix}",c))
            assert anchors
            print(json.dumps(dict(key=key,status="STARTED",anchors=len(anchors))),flush=True)
            row=search(key,anchors,a.checker,a.budget)
            archive.write(json.dumps(row)+"\n")
            archive.flush()
            print(json.dumps({k:v for k,v in row.items() if k!="cases"}),flush=True)
