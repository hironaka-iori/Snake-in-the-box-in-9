"""Rebuild both rooted eight-dimensional layers with explicit disjointness and sizes."""
from concurrent.futures import ProcessPoolExecutor
from search_q9_anchored_sets import search
from verify_q9_center_avoidance import verify
import gzip,json,random
def templates():
    bank={}
    for l in gzip.open("q9_free_bridge_join_inputs.txt.gz","rt"):
        p=list(map(int,l.split()))
        if len(p)!=192:continue
        for d in range(9):
            cuts=[j for j,(a,b) in enumerate(zip(p,p[1:])) if a^b==1<<d]
            if len(cuts)!=1:continue
            i=cuts[0];o=p[i]
            def project(x):
                x^=o;return (x&((1<<d)-1))|((x>>(d+1))<<d)
            arms=[list(map(project,p[i::-1])),list(map(project,p[i+1:]))];arms.sort(key=len,reverse=True)
            table={};key=tuple(tuple(table.setdefault(x^y,len(table)) for x,y in zip(a,a[1:])) for a in arms)
            bank.setdefault(key,arms)
    return list(bank.values())
def work(job):
    i,arms,L,R,mode,s=job;gen=random.Random(s);q=arms[0][::-1]+[v+256 for v in arms[1]];verify(q)
    fixed={0,256}
    for side,arm in enumerate(arms):
        keep=set(range(len(arm)))
        if mode=='sparse':keep=set(gen.sample(sorted(keep),len(arm)*3//5))
        if mode=='runs':
            spans=[(gen.randrange(len(arm)),gen.randrange(5,17)) for _ in range(7)]
            keep={j for j in keep if any(a<=j<a+b for a,b in spans)}
        fixed.update(arm[j]+256*side for j in keep)
    st,p=search(fixed,set(q),L+R+1,20000,rooted_layer_lengths=(L,R))
    if p:
        verify(p);assert len(p)==L+R+2 and sum(v<256 for v in p)==L+1 and sum(a^b==256 for a,b in zip(p,p[1:]))==1
    return [i,L,R,mode,s,st,p]
if __name__=="__main__":
    bank=templates();a,b=bank[0];control=work((0,(a,b),len(a)-1,len(b)-1,'control',1));assert control[5]=='FOUND';print(json.dumps(control),flush=True)
    jobs=[(i,p,L,R,m,1223+17*i) for i,p in enumerate(bank) for L,R in [(96,95),(95,96),(97,94),(94,97),(98,93),(93,98),(97,97),(98,97)] for m in ('sparse','runs')]
    random.Random(1209).shuffle(jobs)
    with ProcessPoolExecutor(2) as pool:
        for r in pool.map(work,jobs,chunksize=1):
            print(json.dumps(r,separators=(",",":")),flush=True)
            if r[-1]:break
