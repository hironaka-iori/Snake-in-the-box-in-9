"""Construct positive inputs by shortening interior connections and audit the C++ witnesses."""
from pathlib import Path
import json, sys
BASE=Path(__file__).resolve().parent
BANK=BASE.parent/"q9_far189_spring_20261121/comparison191.words"
def points(w):
    p=[0]
    for d in w:p.append(p[-1]^1<<int(d))
    return p
def valid(p):
    return all(0<=v<512 for v in p) and len(set(p))==len(p) and all(((x^y).bit_count()==1)==(i==j+1) for i,x in enumerate(p) for j,y in enumerate(p[:i]))
def word(p):
    return "".join(str((x^y).bit_length()-1) for x,y in zip(p,p[1:]))
def shorten(p):
    for i in range(15,len(p)-25):
        for length in (4,5,6,7):
            u,v=p[i],p[i+length]
            if (u^v).bit_count()!=length-2:continue
            from itertools import permutations
            for order in permutations(d for d in range(9) if (u^v)>>d&1):
                q=p[:i+1]
                for d in order:q.append(q[-1]^1<<d)
                q+=p[i+length+1:]
                if valid(q):return word(q)
if sys.argv[1]=="plant":
    count=0
    for w in BANK.read_text().split():
        s=shorten(points(w))
        if s:
            assert len(s)==189
            print(s);count+=1
            if count==8:break
    assert count==8
else:
    targets={"archive192":192,"new189":192,"new189_wide":192,"short193":193,"control":191,"gain2_control":191,"planted":191,"target195":195,"target196":196,"double192":192,"archive_double192":192,"planted_double":191,"second_generation192":192,"remaining192":192,"distant192":192,"distant195":195,"distant196":196}
    output={}
    for label,target in targets.items():
        f=BASE/(label+".log")
        if not f.exists():continue
        rows=[list(map(int,l.split())) for l in f.read_text().splitlines() if l.strip()]
        for row,orientation,hit,geometry,candidates,nodes,cutoffs,*p in rows:
            assert (len(p)==target+1 and valid(p)) if hit else not p
        output[label]={"runs":len(rows),"hits":sum(r[2] for r in rows),"bridge_searches":sum(r[4] for r in rows),"nodes":sum(r[5] for r in rows),"budget_cutoffs":sum(r[6] for r in rows)}
    print(json.dumps(output,indent=2))
