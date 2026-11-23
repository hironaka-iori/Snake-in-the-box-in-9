from pathlib import Path
from itertools import permutations
from collections import defaultdict,Counter
import random,json,sys
D=Path(__file__).resolve().parent;R=D.parent
words=(R/'q9_gap_generations/prior191.words').read_text().split()
def pts(w):
    p=[0]
    for c in w:p.append(p[-1]^1<<int(c))
    return p
def defects(w):
    p=pts(w);n=0;seen=Counter()
    for j,x in enumerate(p):
        n+=seen[x]+sum(seen.get(x^1<<k,0) for k in range(9))-int(j>0);seen[x]+=1
    return n
def norm(w):
    d={};return bytes(d.setdefault(x,len(d)) for x in w)
def parts(w,grp):
    return tuple(''.join(x for x in w if grp[int(x)]==k) for k in range(3))
def lookup(w,g):
    h=parts(w,g)
    return h,tuple(norm(a) for a in h)
def pg(rng):
    q=list(range(9));rng.shuffle(q);return tuple(q[k]//3 for k in range(9))
def reassign(src,target,groups,ga,gb,rng):
    mp={}
    for j in range(3):
        ca=[str(k) for k in range(9) if gb[k]==j];cb=[str(k) for k in range(9) if ga[k]==j]
        best=None
        for v in permutations(cb):
            z=dict(zip(ca,v));w=''.join(z[t] for t in src[j]);t=target[j]
            cost=(sum(x!=y for x,y in zip(w,t)),rng.random())
            if best is None or cost<best[0]:best=(cost,z)
        mp.update(best[1])
    return mp
def main():
    seed,rounds,count=map(int,sys.argv[1:4]);rng=random.Random(seed);tip=len(sys.argv)>4;two=len(sys.argv)>5
    seen=set(); controls=[]; jobs=[];stats=Counter()
    for roundid in range(rounds):
        ga=pg(rng);gb=pg(rng);idx=defaultdict(list);regions=(6,8,10,12,14)
        # Random reservoir per pair of exact projected subwords, where the third subword may differ.
        for b,w in enumerate(words):
            for rev in [0,1]:
                v=w[::-1] if rev else w
                for L in regions:
                    for j in range(rng.randrange(2),192-L,2):
                        donor=v[j:j+L];h,keys=lookup(donor,gb);free=rng.randrange(3)
                        k=(L,free,keys[(free+1)%3],keys[(free+2)%3])
                        bucket=idx[k]
                        if len(bucket)<64:bucket.append((b,rev,j,donor,h))
                        else:
                            u=rng.randrange(500); 
                            if u<64:bucket[u]=(b,rev,j,donor,h)
        for _ in range(count):
            a=rng.randrange(len(words));rev=rng.randrange(2);w=words[a][::-1] if rev else words[a]
            # The two cuts replace separate windows, most often with -1 and +2 changes in length.
            control=(_%12==0); gains=(0,0) if control else rng.choice([(-1,2),(2,-1),(0,1),(1,0),(-2,3),(3,-2)])
            starts=sorted([rng.choice(list(range(0,30))+list(range(146,171))),rng.randrange(44,130)])
            if tip and not control:
                odd=next(v for v in gains if v%2);even=next(v for v in gains if v%2==0)
                if rng.randrange(2):starts=[0,rng.randrange(24,144)];gains=(odd,even)
                else:starts=[rng.randrange(25,146),-1];gains=(even,odd)
            patches=[]
            for ix,(i,gain) in enumerate(zip(starts,gains)):
                L=rng.choice(regions);n=L-gain
                if tip and i in (0,-1):
                    cut=rng.choice([0,0,0,1,2,3,4,5]);i=cut if i==0 else len(w)-n-cut
                u=w[i:i+n];h,keys=lookup(u,ga);free=rng.randrange(3)
                bucket=idx.get((L,free,keys[(free+1)%3],keys[(free+2)%3]),[])
                if two and patches:bucket=[z for z in bucket if z[0]==patches[0]['b']]
                opts=[]
                for b,br,j,v,src in rng.sample(bucket,min(8,len(bucket))):
                    if b==a:continue
                    mp=reassign(src,h,free,ga,gb,rng);new=''.join(mp[t] for t in v)
                    if new==u:continue
                    same=parts(new,ga)==h
                    if control!=same:continue
                    # Force an actual group schedule change, independent of the digit reassignment.
                    newgroups=''.join(str(ga[int(x)]) for x in new);oldgroups=''.join(str(ga[int(x)]) for x in u)
                    if newgroups==oldgroups:continue
                    dist=(pts(new)[-1]^pts(u)[-1]).bit_count()
                    if dist>(gain%2)+(0 if tip and not gain%2 else 2):continue
                    opts.append((dist+rng.random(),dict(at=i,n=n,b=b,rev=br,j=j,L=L,mp=''.join(mp[str(t)] for t in range(9)),piece=new,free=free)))
                if not opts:break
                patches.append(min(opts,key=lambda t:t[0])[1])
            if len(patches)!=2:continue
            # Require the splice maps actually send the second donor's axes to different physical axes in the two windows.
            if patches[0]['mp']==patches[1]['mp']:continue
            v=w
            for e in reversed(patches):v=v[:e['at']]+e['piece']+v[e['at']+e['n']:]
            key=(v,ga)
            if key in seen:continue
            seen.add(key);s=defects(v);stats['generated_control' if control else 'generated_target']+=1
            if control and s==0:continue
            if not control and s>36:continue
            rec=dict(a=a,rev=rev,groups=ga,donor_groups=gb,patches=patches,word=v,defects=s)
            (controls if control else jobs).append(rec)
        print(roundid,len(jobs),len(controls),flush=True)
    jobs.sort(key=lambda r:r['defects']);controls.sort(key=lambda r:r['defects'])
    for name,rs in [('target',jobs),('control',controls)]:
        (D/f'{name}_{seed}.jsonl').write_text(''.join(json.dumps(v,separators=(',',':'))+'\n' for v in rs))
        with (D/f'{name}_{seed}.in').open('w') as f:
            for v in rs:print(v['word'],''.join(map(str,v['groups'])),file=f)
    print(stats)
if __name__=='__main__':main()
