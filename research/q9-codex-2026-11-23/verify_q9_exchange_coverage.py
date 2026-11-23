"""Check coverage of the reported search scopes and the geometry controls."""
import json,math
from pathlib import Path
def sets(name,size):
    rows=[tuple(map(int,l.split())) for l in Path(name).read_text().splitlines()]
    assert len(rows)==len(set(rows))
    assert all(len(r)==len(set(r))==size and all(0<=v<512 and not ((r[0]^v).bit_count()%2) for v in r) for r in rows)
    return rows
def audit(file,groups,arity,n,d,which=None):
    rows=Path(file).read_text().splitlines();assert len(rows)==groups
    tests=0
    for i,l in enumerate(rows):
        t=l.split();assert len(t)==arity and t[0]=="ROW" and int(t[1])==i
        assert int(t[-1])==0 and int(t[3 if arity==7 else 2])==math.comb(n,d)
        if which is None or i in which:tests+=int(t[-2])
    return tests
reps=sets("q9_face_distinct_halves.txt",96); allsets=sets("q9_face_all_halves.txt",96)
assert len(reps)==5342 and len(allsets)==7528
index={s:i for i,s in enumerate(allsets)}
which={index[s] for s in reps};assert len(which)==len(reps)
minority={}
for d,file in enumerate(["q9_face_distinct_zero.log","q9_face_all_one.log","q9_face_distinct_two.log","q9_face_distinct_three.log"]):
    minority[d]=audit(file,len(allsets) if d==1 else len(reps),7,96,d,which if d==1 else None)
major=sets("q9_majority_exchange_sets.txt",97)
assert len(major)==4053
majority={d:audit(f"q9_majority_exchange_{d}.log",len(major),5,97,d) for d in range(3)}
bank=sets("q9_majority_96seeds.txt",96);assert len(bank)==681
gain={d:audit(f"q9_majority_gain_{d}.log",len(bank),5,96,d) for d in range(3)}
print(json.dumps(dict(minority_sets=len(reps),minority_graph_tests=minority,majority_sets=len(major),majority_graph_tests=majority,donor_sets=len(bank),donor_add_one_graph_tests=gain,unresolved=0),indent=2))
