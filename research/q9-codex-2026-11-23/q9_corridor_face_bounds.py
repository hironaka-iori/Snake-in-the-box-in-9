"""Four-cube induced-linear-forest inequalities for a residual nine-cube graph."""
from functools import lru_cache
from itertools import combinations
AX=range(9)
q4_nb=[sum(1<<(v^1<<i) for i in range(4)) for v in range(16)]
q4_indices=[1<<j for j in range(16)]
@lru_cache(maxsize=1)
def bounds():
    ub=bytearray(1<<16)
    for m in range(1,1<<16):
        left=m;forest=True
        while left and forest:
            seed=left&-left;left^=seed;q=[seed.bit_length()-1];twice_e=0
            for x in q:
                ns=q4_nb[x]&m;d=ns.bit_count()
                if d>2:forest=False;break
                twice_e+=d
                for_insert=ns&left;left^=for_insert
                while for_insert:
                    t=for_insert&-for_insert;q.append(t.bit_length()-1);for_insert^=t
            if twice_e>=2*len(q):forest=False
        if forest:ub[m]=m.bit_count()
        else:
            t=m;u=0
            while t:
                bit=t&-t;t^=bit;u=max(u,ub[m^bit])
            ub[m]=u
    assert ub[-1]==8
    return ub

@lru_cache(maxsize=1)
def tables():
    ans=[]
    for axes in combinations(AX,4):
        comp=tuple(x for x in AX if x not in axes)
        proj=lambda v,cols:sum(((v>>a)&1)<<j for j,a in enumerate(cols))
        encode=[(proj(v,comp),1<<proj(v,axes)) for v in range(512)]
        verts=[[None]*16 for _ in range(32)]
        for v,(face,bit) in enumerate(encode):verts[face][bit.bit_length()-1]=v
        ans.append((encode,verts))
    return ans

def strongest(verts,keep=4):
    ub=bounds();ranked=[]
    for idx,(enc,groups) in enumerate(tables()):
        masks=[0]*32
        for v in verts:
            i,bit=enc[v];masks[i]|=bit
        bound=sum(ub[m] for m in masks)
        ranked.append((bound,idx,masks))
    ranked.sort()
    inequalities=[]
    for bound,idx,masks in ranked[:keep]:
        _,groups=tables()[idx]
        for g,m in zip(groups,masks):
            k=ub[m]
            if k<m.bit_count():inequalities.append(([g[j]+1 for j in range(16) if m>>j&1],k))
    return ranked[0][0],inequalities
