"""Compare the paired SAT encoding with explicit orientation enumeration."""
import gzip
import json
import random
import subprocess
import sys
from collections import Counter
from itertools import product
from q9_pair_selector import search
from verify_q9_center_avoidance import verify

rng=random.Random(764013)
with gzip.open("q9_free_bridge_join_inputs.txt.gz","rt") as f:
    paths=[list(map(int,l.split())) for l in f if len(l.split())==192]
counts=Counter()
assignments=0
for i in range(60):
    p=rng.choice(paths)
    cut=rng.choice([0,2,4,6,8])
    # Known-positive lengths also exercise reconstruction.
    if i%2:p=p[:191-cut];side=set(p[1::2])
    else:p=p[:192-cut];side=set(p[rng.randrange(2)::2])
    t=rng.choice([t for t in range(1,512) if not t.bit_count()%2])
    pairs=sorted((x,x^t) for x in side if (x^t) not in side)
    pairs=rng.sample(pairs,min(7,len(pairs)))
    fixed=side-{a for a,b in pairs}
    rows=[]
    for opts in product(*pairs):
        values=sorted(fixed|set(opts))
        rows.append(" ".join(map(str,[len(values),*values])))
    assignments+=len(rows)
    raw=subprocess.run([sys.argv[1],"--sets"],input="\n".join(rows)+"\n",text=True,
                       check=True,capture_output=True).stdout.splitlines()
    assert len(raw)==len(rows) and "UNKNOWN" not in raw
    for line in raw:
        if line.startswith("FOUND "):
            w=list(map(int,line.split()[1:]));verify(w);assert len(w)==2*len(side)+1
    expected="FOUND" if any(l.startswith("FOUND ") for l in raw) else "UNSAT"
    got,w=search(side,pairs,t,set(p),2*len(side),20000)
    assert got==expected,(i,expected,got)
    if w:verify(w)
    counts[got]+=1
print(json.dumps({"tested":sum(counts.values()),"explicit_assignments":assignments,
                  "statuses":counts,"all_agreed":True}))
