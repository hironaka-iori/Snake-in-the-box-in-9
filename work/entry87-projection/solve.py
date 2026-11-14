"""Exact cube-word models for the entry-87 one-chord construction.

Run from any directory with Python 3.11 and python-sat:
  python solve.py --dimension 6 --output six.json
"""
import argparse
from collections import Counter
from hashlib import sha256
from itertools import combinations
import json
import os
from pathlib import Path
import time
from pysat.solvers import Cadical195, pysolvers
from pysat.card import CardEnc, EncType

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


def model(path, bits, conflict_budget=None, anchors=None, certificate=None, anchor_families=()):
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
    clauses=[] if certificate is not None else None
    with Cadical195(with_proof=certificate is not None) as sat:
        def add(clause):
            sat.add_clause(clause)
            if clauses is not None:
                clauses.append(clause)
        for r,domain in enumerate(domains):
            add([lit(r,w) for w in domain])
            for x,y in combinations(domain,2):
                add([-lit(r,x),-lit(r,y)])
            # Canonical first use: the set of coordinates ever used before
            # a position is an initial segment. Its membership is monotone.
            # A bit first appears as 1 in the word after its first transition.
            for c in range(dim):
                seen=1+size*n+dim*r+c
                ones=[lit(r,w) for w in domain if w>>c&1]
                earlier=[seen-dim] if r else []
                add([-seen,*earlier,*ones])
                for alternative in earlier+ones:
                    add([-alternative,seen])
                if c and r:
                    add([-seen,seen-dim-1])
        for (a,b),s in relations.items():
            for left,right in [(a,b),(b,a)]:
                for x in domains[left]:
                    add([-lit(left,x)]+[lit(right,y) for y in domains[right]
                                                   if s>>(x^y).bit_count()&1])
        next_id=n*(size+dim)
        families=list(anchor_families)
        if anchors is not None:
            families.append(anchors)
        for anchors in families:
            assert 0<len(anchors)<=size//2 and len(set(anchors))==len(anchors)
            for a,b in combinations(sorted(anchors),2):
                assert a%2==b%2 and not (relations.get((a,b),1)&1)
            # These distinct words exhaust all words of that parity at equality.
            used=[]
            for w in range(size):
                if w.bit_count()%2!=anchors[0]%2:
                    continue
                literals=[lit(r,w) for r in anchors if w in domains[r]]
                if len(anchors)==size//2:
                    add(literals)
                else:
                    next_id+=1
                    occ=next_id
                    used.append(occ)
                    add([-occ,*literals])
                    for v in literals:
                        add([-v,occ])
                for l1,l2 in combinations(literals,2):
                    add([-l1,-l2])
            if used:
                cap=CardEnc.atmost(lits=[-x for x in used],bound=size//2-len(anchors),
                                   top_id=next_id,encoding=EncType.seqcounter)
                for clause in cap.clauses:
                    add(clause)
                next_id=max(next_id,cap.nv)
        if conflict_budget is None:
            answer=sat.solve()
        else:
            sat.conf_budget(conflict_budget)
            answer=sat.solve_limited()
        result=dict(status={True:"SAT",False:"UNSAT",None:"OPEN"}[answer],
                    reason="CaDiCaL",runs=n,stats=sat.accum_stats())
        if answer is False and certificate is not None:
            nvar=max(abs(x) for clause in clauses for x in clause)
            with certificate.with_suffix(".cnf").open("w",encoding="ascii",newline="\n") as f:
                f.write(f"p cnf {nvar} {len(clauses)}\n")
                for clause in clauses:
                    f.write(" ".join(map(str,clause))+" 0\n")
            proof=certificate.with_suffix(".drat")
            if os.name=="nt":
                # PySAT supplies CaDiCaL's packed proof stream through an open
                # temporary file; decode incrementally to avoid a list of all
                # clauses and a second copy of the binary proof in RAM.
                pysolvers.flushpr(sat.prfp)
                sat.prfile.seek(0)
                with proof.open("wb") as f:
                    mode=None; number=0; shift=0; tokens=[]
                    for block in iter(lambda:sat.prfile.read(1<<20),b""):
                        for char in block:
                            if mode is None:
                                if char not in (97,100):
                                    raise ValueError(("bad DRAT mode",char))
                                mode=char
                                continue
                            if not char:
                                if shift: raise ValueError("unterminated literal")
                                if mode==100: f.write(b"d ")
                                if tokens: f.write(b" ".join(tokens)+b" ")
                                f.write(b"0\n")
                                mode=None; tokens.clear()
                                continue
                            number|=(char&127)<<shift
                            if char&128:
                                shift+=7
                            else:
                                literal=-(number>>1) if number&1 else number>>1
                                tokens.append(str(literal).encode("ascii"));number=0;shift=0
                    if mode is not None: raise ValueError("unfinished proof")
            else:
                with proof.open("w",encoding="ascii",newline="\n") as f:
                    for line in sat.get_proof():
                        f.write(line+"\n")
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
