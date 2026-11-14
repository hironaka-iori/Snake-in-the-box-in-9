"""Construct actual conflicting interval sets for all bankwide certified triples."""
import csv
from collections import Counter
from itertools import combinations
from pathlib import Path
import json
from insertion_shapes import projected_intervals
from touching_families import data
from solve import BANK,save


def precompute():
    near,pairs,universals,single=data()
    allowed=[()]+[(s,) for s in single]+[(a,b) for a,b in combinations(single,2) if near[a]&b]
    schemes=[]
    for J in allowed:
        ok=lambda t:all(near[s]&t for s in J)
        direct=list(J)+[s for s in range(1,256) if (s.bit_count()>=3 or s in universals) and ok(s)]
        pairs2=[(a if ok(a) else 0,b if ok(b) else 0) for a,b in pairs]
        schemes.append((set(direct),pairs2))
    return near,schemes


def witness(tr,schemes):
    best=-1
    for p in (0,1):
        weights=Counter(tr[p::2])
        for take,pairs in schemes:
            shapes=set(weights)&take
            for a,b in pairs:
                c=a if weights[a]>=weights[b] else b
                if weights[c]:
                    shapes.add(c)
            score=sum(weights[s] for s in shapes)
            if score>best:
                best=score
                win=[i for i in range(p,len(tr),2) if tr[i] in shapes]
    return win


if __name__=="__main__":
    bank=[r["vertex_sequence"] for r in json.loads(BANK.read_bytes())]
    rows=list(csv.DictReader(Path("bank-exact-cliques.csv").open(encoding="utf-8-sig")))
    assert {(int(r["entry"]),int(r["retained_mask"])) for r in rows}=={
        (k,sum(1<<b for b in B)) for k in range(131) for B in combinations(range(9),3)}
    near,schemes=precompute()
    counts=Counter();peaks=[]
    classic={(r["entry"],r["retained_mask"]):set(r["excluded_positions"].split())
             for r in csv.DictReader(Path("bank-shape-exclusions.csv").open(encoding="utf-8-sig"))}
    for row in rows:
        k=int(row["entry"]);m=int(row["retained_mask"]);pos=list(map(int,row["excluded_positions"].split()))
        keep=[b for b in range(9) if m>>b&1];p=bank[k]
        assert len(pos)==len(set(pos))==int(row["exclusions"]) and all(0<=j<192 for j in pos)
        assert classic[row["entry"],row["retained_mask"]]<=set(map(str,pos))
        for j in set(pos)|{int(row["sample_position"])}:
            tr=projected_intervals(p[:j+1]+p[j:],keep)
            clique=witness(tr,schemes)
            # Check the exhibited pairs directly on trace types, including
            # identical trace types represented by distinct intervals.
            types=set(tr[i] for i in clique)
            assert len({i%2 for i in clique})==1
            assert all(near[a]&b for a,b in combinations(types,2))
            if j in pos: assert len(clique)>32
            if j==int(row["sample_position"]): assert len(clique)==int(row["peak"])
        counts[k]+=len(pos);peaks.append(int(row["peak"]))
    result=dict(tested=131*84*192,checked_exclusions=sum(counts.values()),peak=max(peaks),
                seed_min=min(counts.values()),seed_max=max(counts.values()),seeds=len(counts))
    save(Path("bank-exact-summary.json"),result)
    print(result)
