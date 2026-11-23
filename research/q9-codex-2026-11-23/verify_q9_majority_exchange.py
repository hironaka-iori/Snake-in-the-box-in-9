"""Cross-check fixed-set and one-exchange queries by enumerating vertex orders."""
from itertools import permutations,combinations
from pathlib import Path
import random,subprocess,json
binary="/tmp/q9-majority-gain-21"
rng=random.Random(4661)
def run(s,drop,gain=0):
    output=subprocess.check_output([binary,str(drop),"200000",str(gain)],input=" ".join(map(str,s))+"\n",text=True).split()
    if output[0]=="FOUND":
        p=[int(x) for x in output[1:]]
        assert len(p)==len(set(p))==2*(len(s)+gain)-1 and min(p)>=0 and max(p)<512
        assert len(set(s)-set(p[::2]))==drop
        assert all(((a^p[j]).bit_count()==1)==(j==i+1) for i,a in enumerate(p) for j in range(i+1,len(p)))
        return True
    assert output[0]=="ROW" and int(output[-1])==0
    return False
def brute(s):
    graph=set()
    for a,b in combinations(s,2):
        diff=a^b
        if diff.bit_count()!=2:continue
        for k in range(9):
            if diff>>k&1 and sum((v^(a^(1<<k))).bit_count()==1 for v in s)==2:
                graph.add((a,b));graph.add((b,a));break
    return any(all(e in graph for e in zip(p,p[1:])) for p in permutations(s))
even=[i for i in range(512) if i.bit_count()%2==0]
stats={}
for i in range(24):
    axes=rng.sample(range(9),6)
    s=rng.sample(even,4) if i%2 else [0,(1<<axes[0])^(1<<axes[1]),sum(1<<a for a in axes[:4]),sum(1<<a for a in axes)]
    for d in range(2):
        expected=brute(s) if not d else any(brute([a for a in s if a!=b]+[v]) for b in s for v in even if v not in s)
        assert run(s,d)==expected
        key=f"{d}_{expected}";stats[key]=stats.get(key,0)+1
p=[0]
for c in Path("q9_reordered_segments_20261120/reference191.words").read_text().splitlines()[0][:-1]:p.append(p[-1]^(1<<int(c)))
s=p[::2]; extras=[v for v in even if v not in s]
for d in range(4):assert run(extras[:d]+s[d:],d)
for d in range(4):assert run(extras[:d]+s[d+1:],d,1)
for i in range(12):
    start=rng.sample(even,4)
    for k in (1,):
        expected=any(brute(start+list(add)) for add in combinations([v for v in even if v not in start],k))
        assert expected==run(start,0,k)
        key=f"gain{k}_{expected}";stats[key]=stats.get(key,0)+1
print(json.dumps(dict(small_trials=stats,positive_test_edges=190,positive_exchange_counts=[0,1,2,3])))
