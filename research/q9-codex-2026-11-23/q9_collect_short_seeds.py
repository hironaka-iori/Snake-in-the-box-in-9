"""Recover independently valid short snakes and remove all reference-bank subpaths."""
import gzip,json
from pathlib import Path
from collections import defaultdict,Counter
def key(w):
    def canon(w):
        labels={};return ''.join(labels.setdefault(c,str(len(labels))) for c in w)
    return min(canon(w),canon(w[::-1]))
def vertices(w):
    p=[0]
    for d in w:p.append(p[-1]^(1<<int(d)))
    return p
def validate(p):
    s=set(p)
    return len(p)==len(s) and all(0<=v<512 for v in p) and all(sum((v^(1<<k)) in s for k in range(9))==(1 if j in (0,len(p)-1) else 2) for j,v in enumerate(p)) and all((a^b).bit_count()==1 for a,b in zip(p,p[1:]))
lengths=range(184,191)
refs=list(gzip.open("q9_dynamic_fold_20261120/reference190.words.gz","rt"))+Path("q9_reordered_segments_20261120/reference191.words").read_text().splitlines()
known={key(w[i:i+n]) for line in refs for w in [line.strip()] for n in lengths for i in range(len(w)-n+1)}
fresh={}; sources=Counter()
def collect(p,label):
    if len(p)<185 or not all(0<=v<512 for v in p):return
    start=0;last={};d=[]
    for j,v in enumerate(p):
        if j:
            bits=p[j-1]^v
            if bits.bit_count()!=1:start=j
            d.append(str(max(0,bits.bit_length()-1)))
        start=max(start,last.get(v,-1)+1)
        for ax in range(9):
            near=last.get(v^(1<<ax),-1)
            if near!=j-1:start=max(start,near+1)
        last[v]=j
        for n in lengths:
            if n>j-start:break
            w=key(d[j-n:j])
            if w not in known and w not in fresh:
                assert validate(vertices(w));fresh[w]=label;sources[label]+=1
files=list(Path("/tmp").glob("q9_97_*.records"))
for f in files:
    for l in f.read_text().splitlines():
        t=l.split();i=len(t)
        while i>0 and t[i-1].isascii() and t[i-1].isdigit() and len(t[i-1])<=3:i-=1
        collect(list(map(int,t[i:])),f.name)
for f in [*Path("/tmp").glob("q9_fresh18*words"),Path("q9_short_route_new189.words")]:
    for line in f.read_text().splitlines():
        if line and set(line)<=set("012345678"):collect(vertices(line),f.name)
with open("q9_nontrunc_short_seeds.words","w") as out:
    for w in sorted(fresh,key=lambda w:(-len(w),w)):print(w,file=out)
sets=defaultdict(set)
for w in fresh:
    p=vertices(w)
    for s in (p[::2],p[1::2]):
        if 92<=len(s)<=96:sets[len(s)].add(tuple(sorted(s)))
for n,ss in sets.items():
    with open(f"q9_nontrunc_short_side{n}.txt","w") as out:
        for s in sorted(ss):print(*s,file=out)
print(json.dumps(dict(reference_subpaths=len(known),lengths=Counter(map(len,fresh)),sources=sources,set_counts={n:len(ss) for n,ss in sets.items()}),indent=2))
