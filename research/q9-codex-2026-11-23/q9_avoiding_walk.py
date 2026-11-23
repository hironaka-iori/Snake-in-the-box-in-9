"""Seek paths beyond known families by regrowing interior intervals on eligible seeds."""
import json,random,time,heapq
from collections import Counter
from q9_avoiding_centers import reference,windows,code
from search_q9_two_flexible_ends import verify
from search_q9_wynn_plateau import moves
NB=[sum(1<<(x^(1<<d)) for d in range(9)) for x in range(512)]
def replace(p,lo,hi,length,limit):
    target=p[hi]
    banned=0
    for v in p[:lo]+p[hi+1:]:banned|=NB[v]|1<<v
    # The fixed endpoints remain mutually visible to detect early chords.
    out=[];tail=[p[lo]]
    def grow(v,left,ban):
        if left==1:
            if (v^target).bit_count()==1:out.append(tuple(p[:lo])+tuple(tail)+tuple(p[hi:]))
            return
        distance=(v^target).bit_count()
        if distance==1 or distance>left:return
        available=NB[v]&~(ban|(1<<target))
        while available and len(out)<limit:
            bit=available&-available;available-=bit
            u=bit.bit_length()-1
            if (u^target).bit_count()==1 and left!=2:continue
            tail.append(u);grow(u,left-1,ban|NB[v]|1<<v);tail.pop()
    grow(p[lo],length,banned)
    return out

def main():
    bank=reference(142);rng=random.Random(2220189)
    seeds=[tuple(r[2]) for r in map(json.loads,open("q9_center_avoiding_seeds.jsonl")) if r[0]=='SEED']
    frontier=[];seen=set();counts=Counter();expanded=0;best=189
    def offer(p):
        nonlocal best
        n=len(p)-1
        if not 186<=n<=194:return
        shape=code([x^y for x,y in zip(p,p[1:])])
        if shape in seen:return
        seen.add(shape)
        if any(z in bank for z in windows(p,142)):return
        counts[n]+=1;heapq.heappush(frontier,(-n+rng.random()*3,rng.random(),p))
        if n>=189:
            verify(p,n)
            print(json.dumps(['SEED',n,list(p)],separators=(',',':')),flush=True)
            if n>=192:raise SystemExit
        best=max(best,n)
    for p in seeds:offer(p)
    start=time.monotonic()
    while frontier and expanded<6000 and time.monotonic()-start<100:
        _,_,p=heapq.heappop(frontier);expanded+=1
        for q in moves(p,186):offer(q)
        for _ in range(36):
            span=rng.randrange(4,16);lo=rng.randrange(len(p)-span);hi=lo+span
            delta=rng.choice([-2,0,0,2,2,4])
            for q in replace(p,lo,hi,span+delta,16):offer(q)
    print(json.dumps(['SUMMARY',expanded,len(seen),dict(counts),len(frontier),best]),flush=True)
if __name__=='__main__':main()
