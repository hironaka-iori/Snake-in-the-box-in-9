"""Certify candidate-specific exclusions using degree conditions and encountered cycle cuts."""
import gzip,json,subprocess,sys,tempfile
from itertools import combinations
from pathlib import Path
from pysat.formula import CNF
from pysat.card import CardEnc,EncType
from pysat.solvers import Cadical195
from q9_adversarial_port_forests import layouts
from verify_q9_222_disconnected import components, NEIGH
from q9_overlapping_port_bound import ROOT

def formula(es):
    R={v for e in es for v in e}
    adj={v:R.intersection(NEIGH[v]) for v in range(512)}
    sat={v for v in R if len(adj[v])==2}
    F={v for v in range(512) if v not in R and len(adj[v])<=2 and not adj[v]&sat}
    cnf=CNF();top=1024
    def card(lits,b,lo):
        nonlocal top
        if (lo and b<=0) or (not lo and b>=len(lits)):return
        if (lo and b>len(lits)) or (not lo and b<0):cnf.append([]);return
        f=(CardEnc.atleast if lo else CardEnc.atmost)(lits,bound=b,top_id=top,encoding=EncType.totalizer)
        top=max(top,f.nv);cnf.extend(f.clauses)
    for parity in range(2):
        fs=[v+1 for v in sorted(F) if v.bit_count()%2==parity]
        card(fs,111-sum(v.bit_count()%2==parity for v in R),True)
    ends=[]
    for v in sorted(R|F):
        guard=[] if v in R else [-v-1]
        L=[w+1 for w in NEIGH[v] if w in F]; need=2-len(adj[v])
        for C in combinations(L,need+1):cnf.append(guard+[-j for j in C])
        end=513+v
        if need:ends.append(end);L=L+[end]
        if len(L)<need:cnf.append(guard)
        elif need:
            for C in combinations(L,len(L)-need+1):cnf.append(guard+list(C))
    card(ends,2,False)
    return cnf,R,F

def run(es,budget,checker,initial=None):
    cnf,R,F=formula(es);cycles=[]
    if initial:
        cycles=initial(R,F)
        for C in cycles:
            T=set(C)
            assert len(T)==len(C) and len(components(T))==1 and all(len(T.intersection(NEIGH[v]))==2 for v in C)
            cnf.append([-v-1 for v in C if v in F])
    for repeat in range(5):
        with Cadical195(bootstrap_with=cnf,with_proof=True) as sat:
            sat.conf_budget(budget);ans=sat.solve_limited()
            if ans is None:return "UNKNOWN",cycles,None
            if ans:
                m=set(sat.get_model());S=R|{v for v in F if v+1 in m}
                new=[sorted(C) for C in components(S) if all(len(C.intersection(NEIGH[v]))==2 for v in C)]
                if not new:return "DEGREE_MODEL",cycles,None
                for C in new:
                    cycles.append(C);cnf.append([-v-1 for v in C if v in F])
                continue
            proof="\n".join(sat.get_proof())+"\n"
        with tempfile.TemporaryDirectory() as d:
            f=Path(d)/"formula";p=Path(d)/"trace";cnf.to_file(str(f));p.write_text(proof)
            c=subprocess.run([checker,str(f),str(p)],capture_output=True)
            assert b"s VERIFIED" in c.stdout,c.stdout[-300:]
        return "DRAT_VERIFIED",cycles,proof
    return "UNKNOWN",cycles,None

if __name__=="__main__":
    all_layouts=list(layouts())
    checker=sys.argv[1]
    with gzip.open(ROOT/"q9_port_adversarial_drat.jsonl.gz","wt") as f:
        for i in map(int,sys.argv[2:]):
            st,cycles,p=run(all_layouts[i],3000,checker)
            print(i,st,len(cycles),flush=True)
            f.write(json.dumps(dict(case=i,edges=all_layouts[i],status=st,cycles=cycles,proof=p))+"\n")
