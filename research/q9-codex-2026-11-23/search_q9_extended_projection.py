"""Try extending a projected Q6 walk by a new base edge and refilling all Q3 fibers."""
import json,sys,random
from collections import Counter
from search_q9_cube_fiber_lift import projections,fiber_solve,verify

def canonical(p):
    labels={};out=[0]
    for a,b in zip(p,p[1:]):
        d=a^b
        out.append(out[-1]^(1<<labels.setdefault(d,len(labels))))
    return bytes(out)

def main():
    rng=random.Random(92031)
    limit=int(sys.argv[2]);cap=int(sys.argv[3])
    bank={}
    for line in open(sys.argv[1]):
        _,*seq=map(int,line.split())
        for p,h in projections(seq,3):
            # Reverse the entire lift and translate both base and fiber origins.
            for walk,parts in ((p,h),(bytes(u^p[-1] for u in p[::-1]),[[x^h[-1][-1] for x in g[::-1]] for g in h[::-1]])):
                q=canonical(walk)
                if q not in bank:bank[q]=parts
    pool={}
    for p,parts in bank.items():
        layers=[0]*64
        for v,g in zip(p,parts):
            for x in g:layers[v]|=1<<x
        tip=p[-1];c=parts[-1][-1]
        for d in range(6):
            v=tip^(1<<d)
            if layers[v]>>c&1:continue
            collisions=sum((layers[v^(1<<k)]>>c)&1 for k in range(6))-1
            collisions+=sum((layers[v]>>(c^(1<<k)))&1 for k in range(3))
            if collisions>2:continue
            q=canonical(p+bytes([v]))
            if q in bank or q in pool:continue
            pool[q]=(collisions,rng.random(),parts+[[c]])
    print('base',len(bank),'pool',len(pool),'collisions',Counter(r[0] for r in pool.values()),file=sys.stderr,flush=True)
    ranked=sorted(pool,key=lambda p:pool[p][:2])[:limit]
    offset=int(sys.argv[4]) if len(sys.argv)>4 else 0
    for p in ranked[offset:]:
        collisions,_,hint=pool[p]
        st,w=fiber_solve(p,3,192,cap,hint)
        if w:assert verify(w) and len(w)>=193
        print(json.dumps([st,p.hex(),collisions,w],separators=(',',':')),flush=True)
        if w:break

if __name__=='__main__':main()
