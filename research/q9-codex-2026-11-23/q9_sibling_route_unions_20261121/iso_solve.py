from pathlib import Path
from collections import defaultdict
from build import D,points
from sat import solve
import json,sys,random
def load(typ):
    seeds={}
    for s in (D/(typ+'.seeds')).read_text().splitlines():
        i,*cs,w=s.split();seeds[int(i)]=(points(w),list(map(int,cs)))
    families=defaultdict(list)
    for ln in (D/(typ+'.isos')).read_text().splitlines():
        i,c,r,l,h,rev,mp,n,*vs=ln.split();n=int(n);vl=list(map(int,vs));assert len(vl)==n*2;i=int(i)
        families[i].append((int(c),int(r),set(vl[:n]),set(vl[n:]),int(l),int(h)))
    return seeds,families
def family(seeds,fams,src,m):
    p,ch=seeds[src];S=set(p);als=fams[src];rng=random.Random(100243*m+41271*src)
    picks=[]
    for bit in (1,2,3):
        opts=[i for i,e in enumerate(als) if e[1]==bit]
        if not opts:continue
        k=(1,3,7,12,18,26,40,9,15)[m%9];rep=m//9
        if rep:opts=sorted(opts,key=lambda i:als[i][0]+rng.uniform(0,3+3*rep))
        covered=set()
        while opts and len(covered)<80 and k>0:
            if m%9 in (3,4,5,6,8):
                sample=opts[:min(len(opts),8+4*rep)]
                ix=max(sample,key=lambda i:len(als[i][2]-covered)-0.17*als[i][0]+rng.random())
            else:ix=opts[0]
            picks.append(ix);covered|=als[ix][2];opts.remove(ix);k-=1
    added=set().union(*(als[j][2] for j in picks));removed=set().union(*(als[j][3] for j in picks))
    hard=S-removed
    # The base walk contributes the unchanged option at each unpinned site.
    if m%9>=2:
        rad=(m%9-1)//2+1
        for j in ch:
            hard.difference_update(p[max(0,j-rad):j+rad+1])
    if m%9 in (4,5,6,8):
        # Some common vertices next to newly available sites can also be replaced.
        common=hard.copy();b=2 if m%9 in (5,6) else 3
        for x in hard:
            if sum((x^(1<<k)) in added for k in range(9))>=b:common.remove(x)
        hard=common
    return p,S|added,hard,picks
def main():
    typ,start,end,ml,mh,cap,tag=sys.argv[1:];start,end,ml,mh,cap=map(int,(start,end,ml,mh,cap));seeds,fs=load(typ);ids=list(fs)
    for i in ids[start:end]:
        for m in range(ml,mh):
            raw,pool,hard,picks=family(seeds,fs,i,m)
            for col in ([None] if typ=='control' else [0,1]):
                rr=solve(pool,hard,raw,len(raw),cap,col);rr.update(src=i,mode=m,hard=len(hard),union=len(pool),majority=col,picks=picks,tag=tag)
                print(json.dumps(rr,separators=(',',':')),flush=True)
                if rr['path'] and typ!='control':return
if __name__=='__main__':main()
