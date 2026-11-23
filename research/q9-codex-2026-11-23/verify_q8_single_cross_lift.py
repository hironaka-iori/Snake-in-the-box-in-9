"""Verify witness geometry, counts, and optionally repeat a complete minimum search in Python."""
import argparse
from collections import Counter,defaultdict
import hashlib
from itertools import permutations
import json
from pathlib import Path
from build_q8_single_cross_bank import BASE,norm,vertices,checked


def placement(path,bank):
    assert len(path)==len(set(path)) and all(0<=x<512 for x in path)
    assert all((u^v).bit_count()==1 for u,v in zip(path,path[1:]))
    seams=[i for i in range(len(path)-1) if path[i]^path[i+1]==256]
    assert len(seams)==1
    s=seams[0];assert path[s]==0 and path[s+1]==256
    a=path[s::-1];b=[x-256 for x in path[s+1:]]
    assert norm(checked(a,8)) in bank and norm(checked(b,8)) in bank
    contacts=[(i,j,path[i],path[j]) for i,u in enumerate(path) for j in range(i+2,len(path)) if (u^path[j]).bit_count()==1]
    assert all((u^v)==256 for i,j,u,v in contacts)
    assert set(a)&set(b)=={0}|{u for i,j,u,v in contacts}
    return (len(b)-1,len(a)-1),contacts


def exchange_steps():
    # Heap's algorithm. Each item gives the two image labels to exchange.
    p=list(range(8));counts=[0]*8;i=0
    while i<8:
        if counts[i]<i:
            j=0 if i%2==0 else counts[i]
            yield p[i],p[j]
            p[i],p[j]=p[j],p[i];counts[i]+=1;i=0
        else:counts[i]=0;i+=1


def rescan(target,bank):
    data=defaultdict(list)
    for w in bank:
        data[len(w)].append(sum(1<<v for v in vertices(tuple(map(int,w)))[1:]))
    mask=(1<<256)-1;ops=[]
    for a,b in exchange_steps():
        a,b=sorted((a,b));gap=(1<<b)-(1<<a)
        low=sum(1<<x for x in range(256) if x>>a&1 and not (x>>b&1));high=low<<gap
        ops.append((low,high,mask^low^high,gap))
    assert len(ops)==40319
    ans={}
    for long in sorted(data,reverse=True):
        short=target-1-long
        if short not in data or short>long:continue
        rotated=data[long][:];others=data[short];bound=257;num=0
        for step in range(40320):
            for r in rotated:
                scores=[(r&s).bit_count() for s in others]
                value=min(scores)
                if value<bound:bound,num=value,0
                if value==bound:num+=scores.count(value)
            if step==40319:break
            low,high,stay,gap=ops[step]
            rotated=[(r&stay)|((r&low)<<gap)|((r&high)>>gap) for r in rotated]
        ans[long,short]=(bound,num)
    return ans


if __name__=='__main__':
    ap=argparse.ArgumentParser();ap.add_argument('--independent',type=int,nargs='*',default=[])
    ns=ap.parse_args();file=BASE/'q8_single_cross_complete_arms.txt'
    bank=set(file.read_text().splitlines());by_len=Counter(map(len,bank));manifest=json.loads((BASE/'q8_single_cross_complete_bank.json').read_text())
    assert hashlib.sha256(file.read_bytes()).hexdigest()==manifest['bank_sha256']
    for w in bank:
        assert norm(w[::-1]) in bank and norm(w)==w
    out={}
    for target in range(192,197):
        path=BASE/f'q8_complete_single_cross_{target}.log';rows={};done=None
        for line in path.read_text().splitlines():
            f=line.split()
            if f[0]=='MIN':
                L,M,c,k=int(f[1]),int(f[2]),int(f[3]),int(f[5])
                w=list(map(int,f[7:]));assert len(w)==target+1
                lengths,contacts=placement(w,bank);assert lengths==(L,M) and len(contacts)==c
                rows[L,M]=(c,k)
            if f[0]=='DONE':done=int(f[3])
        pairs={(v,target-1-v) for v in by_len if target-1-v in by_len and v>=target-1-v}
        assert set(rows)==pairs
        assert done==40320*sum(by_len[a]*by_len[b] for a,b in pairs)
        if target in ns.independent:assert rescan(target,bank)==rows
        out[target]=dict(placements=done,minimum=min(x[0] for x in rows.values()),rows={f'{a}+1+{b}':dict(chords=c,count=k) for (a,b),(c,k) in rows.items()})
    near=[list(map(int,s.split())) for s in (BASE/'q8_complete_single_cross_near_192.txt').read_text().splitlines()]
    hits=[]
    for p in near:
        lengths,contacts=placement(p,bank);assert len(p)==193 and len(contacts)==1
        hits.append(dict(lengths=lengths,contact=contacts[0]))
    pos=[l for l in (BASE/'q8_complete_single_cross_191_control.log').read_text().splitlines() if l.startswith('FOUND')]
    assert len(pos)==1
    p=list(map(int,pos[0].split()[1:]));lens,contacts=placement(p,bank);assert len(p)==192 and not contacts
    print(json.dumps(dict(rooted=by_len,targets=out,near192=hits,control191=lens,independent=ns.independent),indent=2))
