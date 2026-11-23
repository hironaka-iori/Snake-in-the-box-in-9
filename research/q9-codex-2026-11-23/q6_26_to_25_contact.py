import argparse
import json
import subprocess
import tempfile
from itertools import combinations
from pathlib import Path
from pysat.card import CardEnc, EncType
from pysat.formula import CNF, IDPool
from pysat.solvers import Cadical195
from verify_q9_free_dimension_cuts import parts,deg

src=Path("q9_endpoint_distance_checks/q6_26_edge_interfaces.log")
parser=argparse.ArgumentParser()
parser.add_argument("checker")
parser.add_argument("--catalogue",type=Path,default=src)
parser.add_argument("--edges",type=int,default=25)
parser.add_argument("--contacts",type=int,default=1)
args=parser.parse_args()
checker=args.checker
for line in args.catalogue.read_text().splitlines():
    if not line.startswith("representative "):continue
    mask=line.split()[-1]
    A={v for v in range(64) if int(mask,16)>>v&1}
    tips={v for v in A if deg(A,v,6)<2}
    allowed=set(range(64))-(A-tips)
    if len(tips)<args.contacts:
        print(json.dumps(dict(mask=mask,status="NOT_ENOUGH_TIPS")),flush=True)
        continue
    f=CNF()
    pool=IDPool(start_from=65)
    f.extend(CardEnc.atleast([v+1 for v in sorted(tips)],args.contacts,vpool=pool,encoding=EncType.totalizer).clauses)
    es=[]
    for v in sorted(allowed):
        n=sorted({v^(1<<i) for i in range(6)} & allowed)
        for bad in combinations(n,2 if v in tips else 3):
            f.append([-v-1,*(-w-1 for w in bad)])
        for w in n:
            if v>=w:continue
            x=pool.id()
            f.extend([[-x,v+1],[-x,w+1],[x,-v-1,-w-1]])
            es.append(x)
    f.extend(CardEnc.atleast(es,args.edges,vpool=pool,encoding=EncType.totalizer).clauses)
    cuts=[]
    while True:
        with Cadical195(bootstrap_with=f,with_proof=True) as sat:
            if not sat.solve():
                proof="\n".join(sat.get_proof())+"\n"
                with tempfile.TemporaryDirectory() as tmp:
                    cnf=Path(tmp)/"f.cnf"
                    trace=Path(tmp)/"f.drat"
                    f.to_file(str(cnf))
                    trace.write_text(proof)
                    r=subprocess.run([checker,str(cnf),str(trace)],capture_output=True,check=True)
                    assert b"s VERIFIED" in r.stdout
                print(json.dumps(dict(mask=mask,status="UNSAT_DRAT_verified",cuts=cuts,proof=proof)),flush=True)
                break
            B={v for v in allowed if v+1 in sat.get_model()}
        union=A|{64+v for v in B}
        cycles=[sorted(v-64 for v in c if v>=64)
                for c in parts(union,7) if all(deg(c,v,7)==2 for v in c)]
        if not cycles:
            assert len(A&B)>=args.contacts and sum(deg(B,v,6) for v in B)>=2*args.edges
            print(json.dumps(dict(mask=mask,status="SAT_checked",points=sorted(B),contacts=len(A&B))),flush=True)
            break
        for c in cycles:
            assert c
            f.append([-v-1 for v in c])
            cuts.append(c)
