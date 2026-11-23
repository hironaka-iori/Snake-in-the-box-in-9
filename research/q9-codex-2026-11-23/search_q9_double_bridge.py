"""Try two simultaneous reroutes on single-chord extensions of Q9 bank paths."""
import json, sys
from collections import Counter
from pathlib import Path
N=[sum(1<<(v^(1<<j)) for j in range(9)) for v in range(512)]
def valid(p):
    return len(set(p))==len(p) and all(((x^p[j]).bit_count()==1)==(j==i+1) for i,x in enumerate(p) for j in range(i+1,len(p)))
def halo(p):
    mask=0
    for x in p: mask |= N[x] | (1<<x)
    return mask
def bridges(u,t,n,blocked):
    if n==1:
        if (u^t).bit_count()==1: yield ()
        return
    dist=(u^t).bit_count()
    if dist<=1 or dist>n or (dist-n)%2:return
    choices=N[u]&~blocked&~(1<<t)
    if n>2:choices &= ~N[t]
    while choices:
        bit=choices&-choices;choices-=bit
        v=bit.bit_length()-1
        for tail in bridges(v,t,n-1,blocked|N[u]|(1<<u)):
            yield (v,)+tail
def test(p,h,r,k,shift,forbid):
    a=h-r;b=h+r;c=len(p)-1-k
    if a<0 or c<=b+1:return
    start=p[:a+1];mid=p[b:c+1];end=p[-1]
    block=halo(start[:-1]+mid[1:]+[end])|forbid
    for inside in bridges(start[-1],mid[0],2*r+shift,block):
        first=start+list(inside)+mid
        if not valid_fast_attachment(first,end):continue
        block2=halo(first[:-1])
        for last in bridges(first[-1],end,k-shift,block2):
            yield first+list(last)+[end]
def valid_fast_attachment(p,end):
    return all(x!=end and (x^end).bit_count()!=1 for x in (p[0],p[-1]))
def main():
    bank=json.loads(Path(sys.argv[1]).read_text());rs=list(map(int,sys.argv[2].split(',')));ks=list(map(int,sys.argv[3].split(',')))
    stats=Counter()
    for row in bank:
        base=row['vertex_sequence'];assert valid(base)
        for p in [base,base[::-1]]:
            for j in range(9):
                v=p[-1]^(1<<j)
                if v in p:continue
                hits=[i for i,x in enumerate(p[:-1]) if (x^v).bit_count()==1]
                if len(hits)!=1:continue
                stats['seeds']+=1
                h=hits[0]
                for r in rs:
                    for k in ks:
                        if h-r<0 or h+r+1>=len(p)-k:continue
                        for shift in [-2,0,2]:
                            if k-shift<1 or 2*r+shift<1:continue
                            stats['queries']+=1
                            for out in test(p+[v],h,r,k,shift,1<<p[h]):
                                assert len(out)==193 and valid(out)
                                print(json.dumps(out),flush=True);return
    print(dict(stats),flush=True)
if __name__=='__main__': main()
