"""Cross-check corner alternatives and missing sections using direct path enumeration."""
import json
import random
import subprocess
import sys
from collections import Counter
from pathlib import Path

def valid(p):
    return bool(p) and len(set(p))==len(p) and all(0<=v<512 for v in p) and all(
       ((p[i]^p[j]).bit_count()==1)==(j==i+1)
       for j in range(len(p)) for i in range(j))

def fits(x,previous,tip):
    return x not in previous and all((x^w).bit_count()!=1 for w in previous if w!=tip)

def tips(p,l,r):
    if l==r==0:return True
    left=l>0
    tip=p[0] if left else p[-1]
    for d in range(9):
        x=tip^(1<<d)
        if fits(x,p,tip) and tips(([x]+p) if left else p+[x],l-int(left),r-int(not left)):return True
    return False

def direct(core,split,gap,l,r):
    def corners():
        q=[]
        def visit(i):
            if i==len(core):yield list(q);return
            choices=[core[i]]
            if i not in (0,len(core)-1,split-1,split):
                choices.append(core[i-1]^core[i]^core[i+1])
            for x in choices:
                if x in q or any(((w^x).bit_count()==1)!=(j+1==i and i!=split) for j,w in enumerate(q)):continue
                q.append(x);yield from visit(i+1);q.pop()
        yield from visit(0)
    def fill(p,trail):
        if len(trail)==gap-1:
            result=p[:split]+trail+p[split:]
            return valid(result) and tips(result,l,r)
        tip=trail[-1] if trail else p[split-1]
        for d in range(9):
            x=tip^(1<<d)
            if x in p or x in trail:continue
            if (x^p[split]).bit_count()>gap-1-len(trail):continue
            # Recheck all edges at completed bridges, prune accidental contacts now.
            if any((x^w).bit_count()==1 for w in p+trail if w!=tip and w!=p[split]):continue
            if fill(p,trail+[x]):return True
        return False
    for p in corners():
        if (tips(p,l,r) if split<0 else fill(p,[])):return True
    return False

def decode(w):
    p=[0]
    for d in w.strip():p.append(p[-1]^(1<<int(d)))
    return p
rng=random.Random(211922)
bank=[decode(w) for w in Path("q9_reordered_segments_20261120/reference191.words").read_text().splitlines()]
cases=[]
for n in range(160):
    path=rng.choice(bank)
    if n<100:
        start=rng.randrange(165);size=rng.randrange(10,16);p=path[start:start+size]
    else:p=path
    if n%3==0:
        core,split,gap=p,-1,0
    else:
        split=rng.randrange(3,len(p)-5)
        oldgap=rng.randrange(3,min(7,len(p)-split-1))
        core=p[:split]+p[split+oldgap-1:]
        gap=max(2,oldgap+rng.choice([-2,0,0,2]))
    l,r=(rng.randrange(3),rng.randrange(3)) if n<100 else (n%2,(n//2)%2)
    cases.append((core,split,gap,l,r))
# On full-size positive and negative cases use easy, directly certified eligibility
# or a fresh exhaustive route over corner assignments after unary pruning.
def large_ref(core,split,gap,l,r):
    # Remove impossible alternate vertices in independent Python, then direct DFS.
    opts=[]
    for i,x in enumerate(core):
        choices={x}
        if i not in (0,len(core)-1,split-1,split):choices.add(core[i-1]^x^core[i+1])
        opts.append(choices)
    fixed=[i for i,q in enumerate(opts) if len(q)==1]
    for j in fixed:
        v=next(iter(opts[j]))
        for i,q in enumerate(opts):
            if i==j or len(q)==1:continue
            pruned={w for w in q if w!=v and (((w^v).bit_count()==1)==(abs(i-j)==1 and max(i,j)!=split))}
            if not pruned:return False
            if len(pruned)==1:fixed.append(i)
            opts[i]=pruned
    if sum(len(q)>1 for q in opts)>7:return None
    import itertools
    for seq in itertools.product(*opts):
        seq=list(seq)
        if len(seq)!=len(set(seq)) or any(((x^seq[k]).bit_count()==1)!=(k==j+1 and k!=split) for j,x in enumerate(seq) for k in range(j+1,len(seq))):continue
        if split<0:
            if tips(seq,l,r):return True
            continue
        def bridge(part):
            if len(part)==gap-1:
                path=seq[:split]+part+seq[split:]
                return valid(path) and tips(path,l,r)
            tip=(part or seq[:split])[-1]
            for d in range(9):
                v=tip^(1<<d)
                if v in seq or v in part or (v^seq[split]).bit_count()>gap-1-len(part):continue
                if any((v^w).bit_count()==1 for w in seq+part if w!=tip and w!=seq[split]):continue
                if bridge(part+[v]):return True
            return False
        if bridge([]):return True
    return False
lines=[" ".join(map(str,[i,s,g,l,r,*p])) for i,(p,s,g,l,r) in enumerate(cases)]
out=subprocess.run([sys.argv[1]],input="\n".join(lines)+"\n",text=True,capture_output=True,check=True).stdout.splitlines()
assert len(out)==len(cases)
summary=Counter()
for i,((p,s,g,l,r),line) in enumerate(zip(cases,out)):
    idx,ok,nodes,*w=map(int,line.split());assert idx==i
    if ok:assert valid(w) and len(w)==len(p)+(g-1 if s>=0 else 0)+l+r
    expected=direct(p,s,g,l,r) if i<100 else large_ref(p,s,g,l,r)
    if expected is not None:
        assert expected==bool(ok),(i,expected,ok)
        summary["matched_found" if ok else "matched_excluded"]+=1
    else:summary["reference_skipped"]+=1
    if ok and len(w)==192:summary["valid_191_edge_controls"]+=1
print(json.dumps(summary,indent=2))
