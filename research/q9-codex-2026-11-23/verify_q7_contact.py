"""Audit Q7 representatives, SAT traces, and the inference for four Q7 faces."""
import argparse,gzip,itertools,json,subprocess,tempfile
from collections import Counter
from concurrent.futures import ProcessPoolExecutor
from pathlib import Path
from q7_contact_feasibility import ROOT,catalogue,make

def parts(S,n):
    rest=set(S)
    while rest:
        v=rest.pop();q=[v]
        for x in q:
            for d in range(n):
                y=x^(1<<d)
                if y in rest:rest.remove(y);q.append(y)
        yield set(q)

def signature(S):
    keys=[]
    for C in parts(S,7):
        assert len(C)==14
        adj={v:sorted(w for w in C if (v^w).bit_count()==1) for v in C}
        ends=[v for v,N in adj.items() if len(N)==1]
        assert len(ends)==2 and all(1<=len(N)<=2 for N in adj.values())
        for start in ends:
            p=[start];order=[]
            while len(p)<14:
                w=next(w for w in adj[p[-1]] if w not in p)
                d=(p[-1]^w).bit_length()-1;p.append(w)
                if d not in order:order.append(d)
            for tail in itertools.permutations(sorted(set(range(7))-set(order))):
                axes=order+list(tail)
                keys.append(tuple(sorted(sum(((v^start)>>d&1)<<i for i,d in enumerate(axes)) for v in S)))
    return min(keys)

def check_one(r,A,checker):
    assert r["status"]=="UNSAT"
    f,allow=make(A,r["contact"],r["edges"],r["size"])
    for C in r["cuts"]:
        assert len(C)==len(set(C)) and set(C)<=allow
        P=A|{v+128 for v in C}
        assert any(all(sum((v^(1<<i)) in Q for i in range(8))==2 for v in Q) for Q in parts(P,8))
        f.append([-v-1 for v in C])
    with tempfile.TemporaryDirectory() as d:
        cnf=Path(d)/"target.cnf";drat=Path(d)/"trace";f.to_file(str(cnf));drat.write_text(r["proof"])
        res=subprocess.run([checker,str(cnf),str(drat)],capture_output=True)
        assert res.returncode==0 and b"s VERIFIED" in res.stdout,(r["row"],res.stdout[-450:])
    return len(r["cuts"])

def connected(values):
    q=[0];seen={0}
    for i in q:
        for j in (i^1,i^2):
            if j not in seen and not (max(values[i],values[j])==52 and min(values[i],values[j])>=51):
                q.append(j);seen.add(j)
    return len(seen)==4

if __name__=="__main__":
    p=argparse.ArgumentParser();p.add_argument("checker");p.add_argument("archives",nargs="+");a=p.parse_args()
    bank=catalogue();assert len(bank)==len({signature(S) for S in bank})==63
    for archive in a.archives:
        rows=list(map(json.loads,gzip.open(archive,"rt")))
        assert len(rows)==63 and sorted(r["row"] for r in rows)==list(range(63))
        parameters = {(r["contact"], r["edges"], r["size"]) for r in rows}
        assert parameters in ({(1,51,-55)}, {(4,50,-54)})
        print("verified target parameters (contacts, edges, signed size)",parameters,flush=True)
        # PySAT's shared variable pool can be mutated during CNF construction.
        # Separate processes keep each reconstruction isolated.
        with ProcessPoolExecutor(max_workers=3) as ex:
            anchors = (bank[r["row"]] for r in rows)
            cutcounts = list(ex.map(check_one, rows, anchors, itertools.repeat(a.checker)))
        print(archive,"verified",len(cutcounts),"extra cycle clauses",sum(cutcounts),flush=True)
    # Any sum >=204 with four terms <=52 has minimum term >=48.
    feasible=[v for v in itertools.product(range(48,53),repeat=4) if sum(v)>=204 and connected(v)]
    cap=max(sum(v) for v in feasible)
    assert cap==204
    print("four-face edge cap",cap,"equality profiles",sorted({tuple(sorted(v)) for v in feasible if sum(v)==204}))

