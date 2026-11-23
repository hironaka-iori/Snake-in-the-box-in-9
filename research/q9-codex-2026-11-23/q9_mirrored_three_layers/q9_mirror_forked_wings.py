import collections,itertools,json,random,sys
from q9_mirror_fixed_wings import solve,sw
t=int(sys.argv[1]);rng=random.Random(20261120+t)
def key(x):return min(x,sw(x,t-1))
vertices={x for x in range(128) if x<sw(x,t-1)}
adj={x:{key(x^1<<i) for i in range(7)}&vertices for x in vertices}
root={x for x in vertices if x.bit_count()==1}
def bits(q):
    out=0
    for v in q:out|=1<<v
    return out
near={v:bits(nei)|1<<v for v,nei in adj.items()}
def grow():
    no=bits(root-{1});states=[((1,),no)];found=[]
    while states:
        nxt=[];rnd=set()
        for p,forbid in states:
            v=p[-1];free=[x for x in adj[v] if not(forbid>>x&1)]
            if len(p)>=19 and len(free)>=2:
                a,b=rng.sample(free,2)
                found.append((p,a,b))
            for x in free:
                nb=forbid|near[v]
                sig=(x,nb)
                if sig in rnd:continue
                rnd.add(sig);nxt.append((p+(x,),nb))
        rng.shuffle(nxt);states=nxt[:100]
    return found
stats=collections.Counter();unique=set();best=0
for run in range(22):
    seeds=grow();rng.shuffle(seeds);seeds.sort(key=lambda r:-len(r[0]))
    for p,a,b in seeds[:10]:
        if (p,a,b) in unique:continue
        unique.add((p,a,b))
        left=[4*v for v in (*p,a)]
        right=[3+4*v for v in (b,*reversed(p))]
        for goal in (96,max(88,best+1)):
            if goal>96:continue
            status,w=solve(left,right,[],t,goal,1500)
            stats[goal,status]+=1
            if w:
                print(json.dumps(dict(t=t,rooted_common_core=len(p),goal=2*goal,length=len(w)-1,path=w)),flush=True)
                best=max(best,(len(w)-1)//2)
                break
    print(run,len(seeds),best,stats,file=sys.stderr,flush=True)
