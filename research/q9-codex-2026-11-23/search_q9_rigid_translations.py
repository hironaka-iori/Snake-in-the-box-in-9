"""CSP over translations of rigid pieces separated by freely redirectable steps."""
import argparse
from functools import lru_cache
import json
from pathlib import Path
from search_q9_unit_displacements import valid

FULL=(1<<512)-1
LO=[sum(1<<i for i in range(512) if i&(1<<k)==0) for k in range(9)]
def shift(bits,offset):
    while offset:
        b=offset&-offset
        mask=LO[b.bit_length()-1]
        bits=((bits&mask)<<b)|((bits&~mask)>>b)
        offset-=b
    return bits
def expand(bits):
    out=0
    for k,mask in enumerate(LO):
        d=1<<k
        out|=((bits&mask)<<d)|((bits&~mask)>>d)
    return out
def values(mask):
    while mask:
        lsb=mask&-mask
        yield lsb.bit_length()-1
        mask-=lsb

def solve(p,j,axes,cap):
    pieces=[[]];which=0
    for i,x in enumerate(p):
        if i:
            flip=x^p[i-1]
            if i-1!=j and flip & axes[int(i-1>j)]:
                pieces.append([])
        pieces[-1].append(x)
        if i==j:which=len(pieces)-1
    n=len(pieces)
    if any(not valid(piece) for piece in pieces):return "EXCLUDED",0,None
    borders=[l[-1]^r[0] for l,r in zip(pieces,pieces[1:])]
    @lru_cache(None)
    def incompatible(i,k):
        a,b=pieces[i],pieces[k]
        if k==i+1:
            ok=0
            for d in range(9):
                delta=borders[i]^(1<<d)
                if valid(a+[v^delta for v in b]):ok|=1<<delta
            return FULL^ok
        right=sum(1<<v for v in b)
        boundary=right|expand(right)
        bad=0
        for v in a:bad|=shift(boundary,v)
        return bad
    @lru_cache(None)
    def contiguous(i):
        return tuple(values(FULL^incompatible(i,i+1)))
    def propagate(dom):
        revisits=[True]*n;last=[0]*n
        while any(revisits):
            i=min((i for i in range(n) if revisits[i]),key=lambda i:dom[i].bit_count())
            mask=dom[i];revisits[i]=False
            if not mask:return False
            count=mask.bit_count()
            if count<=4 and last[i]!=mask:
                last[i]=mask;placements=list(values(mask))
                for k in range(n):
                    if i==k:continue
                    bad=incompatible(min(i,k),max(i,k));blocked=dom[k]
                    for v in placements:
                        blocked&=shift(bad,v)
                        if not blocked:break
                    if blocked:
                        dom[k]^=blocked;revisits[k]=True
                        if not dom[k]:return False
            else:
                for k in (i-1,i+1):
                    if not 0<=k<n:continue
                    support=0
                    for d in contiguous(min(i,k)):
                        support|=shift(mask,d)
                    kept=dom[k]&support
                    if kept!=dom[k]:
                        dom[k]=kept;revisits[k]=True
                        if not kept:return False
        return True
    nodes=0
    def branch(dom):
        nonlocal nodes
        nodes+=1
        if nodes>cap:return "UNKNOWN",None
        if not propagate(dom):return "EXCLUDED",None
        unknown=[i for i in range(n) if dom[i].bit_count()>1]
        if not unknown:
            w=[v^(dom[i].bit_length()-1) for i,l in enumerate(pieces) for v in l]
            assert valid(w)
            return "FOUND",w
        i=min(unknown,key=lambda i:(dom[i].bit_count(),-len(pieces[i])))
        for v in values(dom[i]):
            child=dom.copy();child[i]=1<<v
            st,w=branch(child)
            if st!="EXCLUDED":return st,w
        return "EXCLUDED",None
    dom=[FULL]*n;dom[which]=1
    st,w=branch(dom)
    return st,nodes,w

if __name__=="__main__":
    import sys
    # Input fields identify the template, and two explicit freely changeable axes.
    for l in sys.stdin:
        idx,t,j,a,b,*p=map(int,l.split())
        assert len(p)==t+1 and all((u^v).bit_count()==1 for u,v in zip(p,p[1:]))
        st,n,w=solve(p,j,(1<<a,1<<b),int(sys.argv[1]))
        print(json.dumps(dict(row=idx,target=t,axes=[a,b],status=st,nodes=n,witness=w)),flush=True)
        if w and t>=192:break
