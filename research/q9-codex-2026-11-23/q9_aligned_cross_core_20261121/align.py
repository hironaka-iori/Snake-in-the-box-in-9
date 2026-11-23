from collections import defaultdict,Counter
from itertools import accumulate
from operator import xor
from pathlib import Path
import json,random,sys

HERE=Path(__file__).resolve().parent; ROOT=HERE.parent
sys.path.insert(0,str(ROOT/'q9_internal_xor_20261121'))
from verify import canon,vertices,chords,wfrom
rng=random.Random(210344)
new=sorted(set((ROOT/'q9_internal_xor_20261121/near192_chords2_outside_plainfiles.words').read_text().split()))
sources={}
for label,files in [('excused',list((ROOT/'q9_excused_frontier').glob('*.words'))),('moving',[ROOT/'q9_moving_chord_first.words']),('old_two',[ROOT/'q9_new189_nearmisses.words']),('record_one',[ROOT/'q9_onechord_expanded_800.txt'])]:
    bank=set()
    for f in files:
        for line in f.read_text().splitlines():
            t=line.split()
            if len(t)==193:w=wfrom(list(map(int,t)))
            elif len(t)==2:
                if t[0]!='2':continue
                w=canon(t[1])
            else:w=canon(t[-1])
            if len(w)==192:bank.add(w)
    sources[label]=sorted(bank)
N=32
def tag(sub):
    return bytes(map(sub.index,sub))
def masks(p):
    return [sum(1<<v for v in p[s::2]) for s in [0,1]]
def bits(x):
    while x:
        b=x&-x;yield b.bit_length()-1;x-=b
def paint(key):
    if key not in tables:
        table=[0]*512
        for v in range(1,512):
            b=v&-v;table[v]=table[v-b]^(1<<key[b.bit_length()-1])
        tables[key]=table
    return tables[key]
tables={}; index=defaultdict(list);donors=[]
for label,words in sources.items():
    for w in words:
        p=vertices(w);assert len(p)==193 and chords(p)
        for oriented in (w,w[::-1]):
            p=vertices(oriented);idx=len(donors);donors.append((label,oriented,p))
            for j in range(0,len(w)-N+1,4):
                index[tag(oriented[j:j+N])].append((idx,j))
print(json.dumps(dict(source_sizes={k:len(v) for k,v in sources.items()},query=len(new))),flush=True)
rng.shuffle(new);counts=Counter();tested=0;seen=set();out=(HERE/'cases.dat').open('w');meta=(HERE/'cases.jsonl').open('w')
limit=int(sys.argv[1]) if len(sys.argv)>1 else 35
for t,w in enumerate(new):
    p=vertices(w); assert len(chords(p))==2
    halves=masks(p)
    for i in rng.sample(range(len(w)-N+1),12):
        s=w[i:i+N];bucket=index[tag(s)]
        if not bucket:continue
        for idx,j in rng.sample(bucket,min(5,len(bucket))):
            label,wd,pd=donors[idx];sub=wd[j:j+N];mp={int(a):int(b) for a,b in zip(sub,s)}
            left=sorted(set(range(9))-set(mp));right=sorted(set(range(9))-set(mp.values()));rng.shuffle(right);mp.update(zip(left,right))
            table=paint(tuple(mp[i] for i in range(9)));trans=table[pd[j]]^p[i]
            assert all((table[pd[j+k]]^trans)==p[i+k] for k in (0,N//2,N))
            tested+=1
            # Keep equal-size sectors, so distance is the number exchanged on each side.
            if (i-j)%2:continue
            for side,a in enumerate(halves):
                b=sum(1<<(table[v]^trans) for v in pd[side::2])
                if (a^b).bit_count()%2:raise AssertionError
                d=(a^b).bit_count()//2
                if not 5<=d<=15 or counts[side,d]>=limit:continue
                c=a&b;u=a^b
                if (c,u) in seen:continue
                seen.add((c,u));counts[side,d]+=1
                anchor=list(bits(c));pool=list(bits(u))
                print(len(anchor)+d,len(anchor),len(pool),*anchor,*pool,file=out)
                print(json.dumps(dict(query=w,donor=wd,source=label,query_offset=i,donor_offset=j,shared_steps=N,permutation=list(mp[k] for k in range(9)),translation=trans,side=side,exchange_distance=d)),file=meta)
    if len(seen)==22*limit:break
print(json.dumps(dict(tested_alignments=tested,regions=len(seen),strata={str(k):v for k,v in sorted(counts.items())})))
