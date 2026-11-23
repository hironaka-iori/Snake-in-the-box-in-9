"""Align two donors on a 24-edge window, splice part of one checkerboard and rebuild its complement."""
import gzip,json,random,sys
from collections import defaultdict
from itertools import permutations
from search_q9_unordered_projection import project
from search_q9_flexible_columns import complete
from verify_q9_center_avoidance import verify
bank=[list(map(int,s.split())) for s in gzip.open('q9_port_followup_public191.txt.gz','rt')]
bank.extend(list(map(int,s.split())) for s in open('q9_port_all_new_plateau.txt'))
groups=defaultdict(list)
for i,p in enumerate(bank):
    for q in (p,p[::-1]):
        w=[(x^y).bit_length()-1 for x,y in zip(q,q[1:])]
        for j in range(0,len(w)-23,3):
            part=w[j:j+24];axes=tuple(dict.fromkeys(part))
            if len(axes)>=5:groups[bytes(axes.index(d) for d in part)].append((i,axes,q[j]))
groups=[g for g in groups.values() if len({v[0] for v in g})>1]
def evenhalf(p,d,c):
    return {v for v in project(p,d) if (v%256).bit_count()%2==c}
def mask(h):return sum(1<<v for v in h)
def solve(h,c,n,budget):
    cols={x%256 for x in h};patch={v for v in range(256) if v.bit_count()%2!=c}
    return complete(h,cols,patch,n,budget,0,cols,c)
def aligned(A,B):
    i,ax,x=A;j,bx,y=B;best=-1;out=None;S=set(bank[i])
    for order in permutations(sorted(set(range(9))-set(ax))):
        coord=dict(zip(bx+tuple(sorted(set(range(9))-set(bx))),ax+order))
        lut=[0]
        for d in range(9):lut += [z^(1<<coord[d]) for z in lut]
        q=[x^lut[z^y] for z in bank[j]];score=sum(v in S for v in q)
        if score>best:out=q;best=score
    return out,best
def main():
    n,budget=map(int,sys.argv[1:3]);rng=random.Random(938462);seen=set()
    st,w=solve(evenhalf(bank[0],8,0),0,191,150000);assert st=='FOUND';verify(w)
    print(json.dumps(['control',st,w]),flush=True)
    if len(sys.argv)>3:
        for row in map(json.loads,open(sys.argv[3])):
            if row[0]=='control' or row[-2]!='UNKNOWN':continue
            m=int(row[-3],16);h={v for v in range(512) if m>>v&1}
            st,w=solve(h,row[4],192,budget)
            print(json.dumps(row[:-2]+[st,w],separators=(',',':')),flush=True)
            if w:return
        return
    known={mask(evenhalf(p,d,c)) for p in bank for d in range(9) for c in (0,1)}
    for trial in range(200000):
        A,B=rng.sample(rng.choice(groups),2)
        if A[0]==B[0]:continue
        q,o=aligned(A,B)
        if o>188:continue
        d=rng.randrange(9);c=rng.randrange(2);u=evenhalf(bank[A[0]],d,c);v=evenhalf(q,d,c)
        center=rng.randrange(256);bit=1<<rng.randrange(8)
        for mode in range(4):
            def use(z):
                x=(z%256)^center
                return (x&bit)==0 if mode==0 else x.bit_count()<=mode+1
            h={x for x in u if not use(x)}|{x for x in v if use(x)}
            m=mask(h)
            if min(len(h^u),len(h^v))<3 or m in known or m in seen:continue
            seen.add(m);st,w=solve(h,c,192,budget)
            print(json.dumps([A[0],B[0],o,d,c,mode,format(m,'x'),st,w],separators=(',',':')),flush=True)
            if w or len(seen)>=n:return
if __name__=='__main__':main()
