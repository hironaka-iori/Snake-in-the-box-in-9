"""Audit half-set coverage and check the pruning logic against small exhaustive cases."""
import gzip,json,math,random,subprocess,sys
from collections import Counter
from itertools import combinations
from pathlib import Path
from functools import lru_cache

def decode(word):
    p=[0]
    for c in word.strip():p.append(p[-1]^(1<<int(c)))
    return p
def valid(p):
    return len(p)==len(set(p)) and all(0<=v<512 for v in p) and all(
      ((p[i]^v).bit_count()==1)==(i+1==j) for j,v in enumerate(p) for i in range(j))
def canon(word):
    def norm(w):
        labels={};return tuple(labels.setdefault(c,len(labels)) for c in w)
    return min(norm(word),norm(word[::-1]))
def external_solve(goal,drops,s):
    run=subprocess.run([sys.argv[1],str(goal),str(drops),"0","1","sets"],input=" ".join(map(str,s))+"\n",text=True,capture_output=True,check=True)
    items=run.stdout.split()
    if items[0]=="FOUND":
        w=list(map(int,items[1:]));assert valid(w) and len(w)==goal+1
        assert len(set(s)-set(w[1::2]))==drops
        return True,w
    assert items[0]=="ROW" and items[-1]=="0"
    return False,None
def exact_small(s):
    # Construct every possible connector, enumerate all orders of the minority vertices
    # and test the two free endpoint slots.
    from itertools import permutations
    s=set(s);neighbors={v:{v^(1<<i) for i in range(9)} for v in s}
    def eligible(v,ends):
        return all(v not in neighbors[w] for w in s-ends)
    for order in permutations(s):
        if not all(any(eligible(v,{x,y}) for v in neighbors[x]&neighbors[y]) for x,y in zip(order,order[1:])):continue
        if all(any(eligible(v,{x}) for v in neighbors[x]) for x in [order[0],order[-1]]):return True
    return False
rng=random.Random(122139);tiny=Counter()
for k in range(32):
    if k%2:
        s=rng.sample([i for i in range(512) if i.bit_count()%2==0],3)
    else:
        axes=rng.sample(range(9),4);s=[0,2**axes[0]+2**axes[1],sum(2**d for d in axes)]
    ok,w=external_solve(6,0,s);assert exact_small(s)==ok;tiny[str(ok)]+=1
    if k<8:
        possible=[i for i in range(512) if i.bit_count()%2==0 and i not in s]
        expected=any(exact_small([x for x in s if x!=v]+[z]) for v in s for z in possible)
        ok,w=external_solve(6,1,s);assert ok==expected;tiny["exchange_"+str(ok)]+=1
s=[0,15,240,255]; ok,w=external_solve(8,1,s);assert not ok;tiny["exchange_False"]+=1
base=decode(Path("q9_reordered_segments_20261120/reference191.words").read_text().splitlines()[0])[:-1]
assert valid(base) and len(base)==191
good=sorted(base[1::2]);unused=[v for v in range(512) if v not in good and (v^good[0]).bit_count()%2==0]
controls=[]
for drop in range(5):
    original=unused[:drop]+good[drop:];ok,w=external_solve(190,drop,original);assert ok;controls.append(dict(exchanges=drop,edges=len(w)-1))
initial=[w.strip() for w in gzip.open("q9_dynamic_fold_20261120/reference190.words.gz","rt")]
prior={canon(w) for w in initial};trimmed={canon(w[k:k+189]) for w in initial for k in (0,1)}
new=Path("q9_short_route_new189.words").read_text().splitlines()
assert len(prior)==1042 and len({canon(w) for w in new})==len(new)==51
assert all(len(w)==189 and valid(decode(w)) and canon(w) not in trimmed for w in new)
halves=[tuple(map(int,l.split())) for l in Path("q9_onechord_minority_sets.txt").read_text().splitlines()]
original=[list(map(int,l.split())) for l in Path("q9_onechord_expanded_800.txt").read_text().splitlines()]
assert len(original)==800 and len(halves)==len(set(halves))==302 and set(halves)=={tuple(sorted(p[1::2])) for p in original}
neighbors=[tuple(v^(1<<i) for i in range(9)) for v in range(512)]
def possible(s):
    hist=Counter(v for x in s for v in neighbors[x])
    return (sum(n==1 for n in hist.values())>=2 and sum(n==2 for n in hist.values())>=len(s)-1 and
        all(sum(hist[x]<=2 for x in neighbors[v])>=2 for v in s))
def audit_rows(filename,n,drops,gain,expected):
    rows=[list(map(int,l.split()[1:])) for l in Path(filename).read_text().splitlines() if l.startswith("ROW ")]
    assert len(rows)==len(expected) and {(r[0],r[1]) for r in rows}==set(expected)
    assert all(r[-1]==0 for r in rows)
    fam=math.comb(n,drops)*math.comb(256-n,drops+gain)
    if filename in ("q9_new189_add_one.log","q9_new189_replace_one.log"):
        assert all(r[2]==fam for r in rows)
    else:assert all(r[2]==math.comb(n,drops) for r in rows)
    return {"starting_sets":len(rows),"set_choices_with_multiplicity":fam*len(rows),"passed_degree_tests":sum(r[-2] for r in rows),"unresolved":sum(r[-1] for r in rows)}
control_rows=[list(map(int,l.split()[1:])) for l in open("q9_onechord_parity_zero.log")]
assert all(bool(row[-2])==possible(halves[row[0]]) for row in control_rows)
for subset,k in [(halves[3],3),(halves[67],67)]:
    # Exhaustively recompute every one-for-one degree bound for this starting set.
    old=set(subset);pool=[x for x in range(512) if (x^subset[0]).bit_count()%2==0 and x not in old]
    count=sum(possible((old-{x})|{y}) for x in old for y in pool)
    row=list(map(int,Path("q9_onechord_parity_one.log").read_text().splitlines()[k].split()[1:]))
    assert row[-2]==count
result={"verified_nontruncation_189":len(new),"compared_190_classes":len(prior),"tiny_crosschecks":tiny,"positive_controls":controls,"800_walks_302_halfsets":{},"51_paths_both_halfsets":{}}
for drops,name in enumerate(["zero","one","two","three"]):
    result["800_walks_302_halfsets"][drops]=audit_rows("q9_onechord_parity_"+name+".log",96,drops,0,[(i,0) for i in range(302)])
for drops,name in enumerate(["add_one","replace_one","two_drops","three_drops"]):
    result["51_paths_both_halfsets"][drops]=audit_rows("q9_new189_"+name+".log",95,drops,1,[(i,h) for i in range(51) for h in range(2)])
print(json.dumps(result,indent=2))
