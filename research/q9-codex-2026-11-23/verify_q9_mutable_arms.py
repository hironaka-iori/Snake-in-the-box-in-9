"""Audit inputs, exact model coverage, positive controls and a small exhaustive cross-check."""
from collections import Counter
from itertools import combinations
from pathlib import Path
import json
import random
from search_q9_rigid_translations import solve

def checked(p):
    return len(set(p))==len(p) and all(0<=v<512 for v in p) and all(
        ((v^w).bit_count()==1)==(j==i+1) for (i,v),(j,w) in combinations(enumerate(p),2))

def brute(p,j,masks):
    # Translation allows normalizing the first vertex of any solution to zero.
    def walk(q):
        k=len(q)-1
        if k==len(p)-1:return True
        step=p[k]^p[k+1]
        choices=[1<<d for d in range(9)] if k!=j and step&masks[int(k>j)] else [step]
        for x in choices:
            v=q[-1]^x
            if v not in q and all((v^w).bit_count()!=1 for w in q[:-1]) and walk(q+[v]):return True
        return False
    return walk([0])
rng=random.Random(20261121)
checks=Counter()
for _ in range(160):
    p=[0]
    for k in range(rng.randrange(4,10)):p.append(p[-1]^(1<<rng.randrange(5)))
    j=rng.randrange(len(p)-1)
    masks=tuple(1<<rng.randrange(5) for h in range(2))
    expected=brute(p,j,masks)
    st,_,w=solve(p,j,masks,100000)
    assert st==("FOUND" if expected else "EXCLUDED") and (w is None or checked(w))
    checks[st]+=1

bank={}
for l in Path("q9_mutable_arm_inputs.txt").read_text().splitlines():
    i,t,j,*p=map(int,l.split());assert len(p)==t+1 and (p[j]^p[j+1])==256
    bank[i]=t
initial={}
def read(name):
    return [json.loads(l) for l in Path(name).read_text().splitlines()]
for f in ["q9_rigid_target192.jsonl","q9_rigid_target193.jsonl","q9_rigid_target194.jsonl","q9_rigid_195_196.jsonl"]:
    for r in read(f):
        key=(r["row"],*r["axes"])
        assert key not in initial and r["target"]==bank[key[0]]
        initial[key]=r["status"]
for r in read("q9_rigid_195_196_retry.jsonl"):
    key=(r["row"],*r["axes"])
    assert initial[key]=="UNKNOWN";initial[key]=r["status"]
extra=Path("q9_rigid_small_retry.jsonl")
if extra.exists():
    for r in read(extra.name):
        key=(r["row"],*r["axes"])
        assert initial[key]=="UNKNOWN";initial[key]=r["status"]
assert set(initial)=={(idx,a,b) for idx in bank for a in range(8) for b in range(8)}
positive=read("q9_rigid_control191.jsonl")[0]["witness"]
assert len(positive)==192 and checked(positive)
d=json.loads(Path("q8_single_cross_chords_20261120/minimum_chord_witnesses.json").read_text())
parents=[]
for family in d.values():
    for row in family:
        p=row["witness"]["vertices"]
        assert len(set(p))==len(p) and all((a^b).bit_count()==1 for a,b in zip(p,p[1:]))
        chord=sum((v^w).bit_count()==1 and j>i+1 for (i,v),(j,w) in combinations(enumerate(p),2))
        assert chord==row["minimum_chords"]
        parents.append(dict(edges=len(p)-1,arms=row["arms"],chords=chord))
print(json.dumps(dict(source_parents=parents,templates=dict(Counter(bank.values())),
    assignments={t:dict(Counter(st for k,st in initial.items() if bank[k[0]]==t)) for t in sorted(set(bank.values()))},
    tiny_reference_tests=dict(checks),positive_control_edges=len(positive)-1),indent=2))
