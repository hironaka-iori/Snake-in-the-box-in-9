"""Replace one projected base edge by three around a Q6 square, then refill Q3."""
import sys,json,random
from collections import Counter
from search_q9_cube_fiber_lift import projections,fiber_solve,verify
from search_q9_extended_projection import canonical

def run(filename,budget,cap):
    bank={}
    for line in open(filename):
        _,*seq=map(int,line.split())
        for p,h in projections(seq,3):bank.setdefault(p,h)
    rng=random.Random(391226)
    keys=list(bank);rng.shuffle(keys)
    seen=set();all_costs=Counter();solved=0
    for p in keys:
        h=bank[p]
        actual={v+64*c for v,g in zip(p,h) for c in g}
        neighbors=Counter(t^(1<<d) for t in actual for d in range(9))
        options=[]
        for i,(u,v) in enumerate(zip(p,p[1:])):
            c=h[i][-1];assert c==h[i+1][0]
            for d in range(6):
                a=u^(1<<d);b=v^(1<<d)
                x=a+64*c;y=b+64*c
                if x in actual or y in actual:continue
                # The old edge is a chord; each added site has one mandated neighbor in the original lift.
                cost=1+neighbors[x]+neighbors[y]-2
                if cost<=2:options.append((cost,rng.random(),i,a,b,c))
        for cost,_,i,a,b,c in sorted(options):
            q=canonical(p[:i+1]+bytes([a,b])+p[i+1:])
            if q in seen or q in bank:continue
            seen.add(q);all_costs[cost]+=1
            phases=h[:i+1]+[[c],[c]]+h[i+1:]
            st,w=fiber_solve(q,3,192,cap,phases)
            if w:assert len(w)>=193 and verify(w)
            print(json.dumps([st,q.hex(),cost,w],separators=(',',':')),flush=True);solved+=1
            if w or solved>=budget:return
    print('all skeletons processed',dict(all_costs),file=sys.stderr)
if __name__=="__main__":run(sys.argv[1],int(sys.argv[2]),int(sys.argv[3]))
