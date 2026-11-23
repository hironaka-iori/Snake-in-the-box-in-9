from concurrent.futures import ProcessPoolExecutor
from search_q9_rotating_coils import types,order,graph
from verify_q9_center_avoidance import verify
from collections import Counter
import json,subprocess
def work(job):
    cls,goal,cap,first,last=job;perm=[];flip=0
    for size,neg in cls:
        j=len(perm);perm.extend(j+(i+1)%size for i in range(size));flip|=neg<<j
    inp=" ".join(map(str,[0,len(perm),order(cls),goal,cap,first,last,flip,*perm]))+"\n"
    st,n,nodes,cycles,*raw=subprocess.check_output(["/tmp/q9_rotation_quotient20"],input=inp,text=True).split()
    w=None
    if st=="FOUND":
        w=list(map(int,raw));assert len(w)==goal and len(set(w))==goal
        assert all(((v^w[j]).bit_count()==1)==(i+1==j or (i==0 and j+1==goal)) for i,v in enumerate(w) for j in range(i+1,goal))
        verify(w[:-1])
    return cls,goal,first,last,st,int(n),int(nodes),int(cycles),w
if __name__=="__main__":
    controls=Counter()
    for cls in types(4):
        d=order(cls)
        if d<2:continue
        dim,orb,own,allowed,adj=graph(cls)
        attainable=set()
        for mask in range(1,1<<len(allowed)):
            chosen={i for j,i in enumerate(sorted(allowed)) if mask>>j&1}
            if any(adj[i][i] for i in chosen):continue  # no reflected cycle with an internal edge
            vs={v for i in chosen for v in orb[i]}
            neighbors={v:[v^1<<j for j in range(dim) if v^1<<j in vs] for v in vs}
            if any(len(nb)!=2 for nb in neighbors.values()):continue
            seen={min(vs)};queue=list(seen)
            for v in queue:
                for u in neighbors[v]:
                    if u not in seen:seen.add(u);queue.append(u)
            if seen==vs:attainable.add(len(vs))
        for g in range(4,17,2):
            if g%d or g//d<3:continue
            r=work((cls,g,1000000,0,-1));assert (r[4]=="FOUND")==(g in attainable) and r[4]!="UNKNOWN"
            controls[r[4]]+=1
    print(json.dumps(dict(controls=controls)),flush=True)
    todo=sorted(((c,g,2000000,0,-1) for c in types(9) if order(c)>=2 for g in range(194,209,2) if not g%order(c)),key=lambda z:(-order(z[0]),z[1],z[0]))
    with ProcessPoolExecutor(4) as pool:
        for r in pool.map(work,todo,chunksize=1,buffersize=32):
            print(json.dumps(r,separators=(",",":")),flush=True)
            if r[-1]:break
