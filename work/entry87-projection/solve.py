"""Exact cube-word models for the entry-87 one-chord construction.

Run from any directory with Python 3.11 and python-sat:
  python solve.py --dimension 6 --output six.json
"""
import argparse
from collections import Counter
from hashlib import sha256
from itertools import combinations
import json
from pathlib import Path
import time
from pysat.solvers import Cadical195

HERE = Path(__file__).resolve().parent
BANK = HERE.parents[1] / "milestones/204-cyclic-symmetry/data/bank9-input.json"
BANK_HASH = "0b973ddcd371680ad4efe07c01008c29437280514926daf1a67d99b6ba510edb"


def paths():
    raw = BANK.read_bytes()
    assert sha256(raw).hexdigest() == BANK_HASH
    bank = json.loads(raw)
    source = bank[87]["vertex_sequence"]
    target = source[:191] + [source[190] ^ 16, source[191] ^ 16]
    assert not defects(source) and defects(target) == [(7,192,70,68)]
    return source, target


def defects(path):
    assert all(0<=x<512 for x in path)
    return [(i,j,path[i],v) for j,v in enumerate(path) for i in range(j)
            if ((v^path[i]).bit_count()!=1 if i+1==j else (v^path[i]).bit_count()<2)]


def model(path, bits, conflict_budget=None):
    mask=sum(1<<b for b in bits)
    dim=len(bits)
    size=1<<dim
    base=[x & ~mask for x in path]
    run=[0]
    for left,right in zip(base,base[1:]):
        assert (left^right).bit_count()<=1
        run.append(run[-1]+(left==right))
    n=run[-1]+1
    domains=[[w for w in range(size) if w.bit_count()%2==r%2] for r in range(n)]
    domains[0]=[0]
    if n>1:
        domains[1]=[1]
    relations={}
    for j,z in enumerate(base):
        for i in range(j):
            d=(base[i]^z).bit_count()
            if d>1:
                continue
            a,b=run[i],run[j]
            allowed=sum(1<<h for h in range((b-a)%2,dim+1,2))
            rule=(1<<(1-d)) if i+1==j else ~((1<<(2-d))-1)
            if a==b:
                if not rule&1:
                    return dict(status="UNSAT",reason="forced equality",runs=n)
            elif allowed&rule!=allowed:
                s=relations.get((a,b),allowed)&rule
                if not s:
                    return dict(status="UNSAT",reason="empty relation",runs=n)
                relations[a,b]=s
    def lit(r,w):
        return 1+size*r+w
    def decode(chosen):
        return [z|sum(((chosen[r]>>i)&1)<<c for i,c in enumerate(bits)) for z,r in zip(base,run)]
    with Cadical195() as sat:
        for r,domain in enumerate(domains):
            sat.add_clause([lit(r,w) for w in domain])
            for x,y in combinations(domain,2):
                sat.add_clause([-lit(r,x),-lit(r,y)])
            # Canonical first use: the set of coordinates ever used before
            # a position is an initial segment. Its membership is monotone.
            # A bit first appears as 1 in the word after its first transition.
            for c in range(dim):
                seen=1+size*n+dim*r+c
                ones=[lit(r,w) for w in domain if w>>c&1]
                earlier=[seen-dim] if r else []
                sat.add_clause([-seen,*earlier,*ones])
                for alternative in earlier+ones:
                    sat.add_clause([-alternative,seen])
                if c and r:
                    sat.add_clause([-seen,seen-dim-1])
        for (a,b),s in relations.items():
            for left,right in [(a,b),(b,a)]:
                for x in domains[left]:
                    sat.add_clause([-lit(left,x)]+[lit(right,y) for y in domains[right]
                                                   if s>>(x^y).bit_count()&1])
        if conflict_budget is None:
            answer=sat.solve()
        else:
            sat.conf_budget(conflict_budget)
            answer=sat.solve_limited()
        result=dict(status={True:"SAT",False:"UNSAT",None:"OPEN"}[answer],
                    reason="CaDiCaL",runs=n,stats=sat.accum_stats())
        if answer:
            positive=set(v for v in sat.get_model() if v>0)
            chosen=[next(w for w in domain if lit(r,w) in positive) for r,domain in enumerate(domains)]
            result["vertices"]=decode(chosen)
            assert not defects(result["vertices"])
            assert all(not((x^y)&~mask) for x,y in zip(path,result["vertices"]))
        return result


def save(file,data):
    tmp=file.with_suffix(".tmp")
    tmp.write_text(json.dumps(data,indent=2)+"\n",encoding="utf-8")
    for i in range(20):
        try:
            tmp.replace(file)
            return
        except PermissionError:
            time.sleep(0.1*(i+1))
    tmp.replace(file)


def main():
    ap=argparse.ArgumentParser()
    ap.add_argument("--dimension",type=int,choices=range(1,10),default=6)
    ap.add_argument("--output",type=Path,required=True)
    ap.add_argument("--budget",type=int)
    args=ap.parse_args()
    source,target=paths()
    frequency=Counter((a^b).bit_length()-1 for a,b in zip(target,target[1:]))
    masks=sorted(combinations(range(9),args.dimension),
                 key=lambda m:(not(1 in m and 4 in m),sum(frequency[b] for b in m),m))
    data=dict(bank_sha256=BANK_HASH,dimension=args.dimension,budget=args.budget,cases=[])
    known=set()
    if args.output.exists():
        data=json.loads(args.output.read_text())
        assert (data["bank_sha256"],data["dimension"],data["budget"])==(BANK_HASH,args.dimension,args.budget)
        known={tuple(r["bits"]) for r in data["cases"]}
    for bits in masks:
        if bits in known:
            continue
        start=time.monotonic()
        result=model(target,bits,args.budget)
        row=dict(bits=list(bits),seconds=round(time.monotonic()-start,3),**result)
        data["cases"].append(row)
        save(args.output,data)
        print(bits,row["status"],row["seconds"],flush=True)
        if row["status"]=="SAT":
            break


if __name__=="__main__":
    main()
