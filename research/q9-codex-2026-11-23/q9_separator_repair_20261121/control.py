import itertools,json,random
from prepare import D,R,NB,graph,parts,majority
from solve import solve,valid
rng=random.Random(39731)
W=(R/'q9_gap_generations/prior190.words').read_text().splitlines()
def control():
    for t in range(6000):
        row=rng.randrange(len(W));word=W[row];p=[0]
        for d in map(int,word):p.append(p[-1]^(1<<d))
        Astar=set(p[::2]);assert len(Astar)==96 and valid(p)
        j=2*rng.randrange(5,90)+1;m=p[j];x,y=p[j-1],p[j+1];blocker=rng.choice(sorted(NB[m]-Astar))
        lost=set(rng.sample(sorted(Astar-{x,y}),5))
        allnew={v for v in range(512) if v.bit_count()%2==0 and v not in Astar|{blocker}}
        extras={blocker}
        for a in sorted(lost)[:4]:
            pool=sorted(v for v in allnew-extras if (v^a).bit_count()==2 and v not in NB[m])
            extras.add(rng.choice(pool))
        A=(Astar-lost)|extras;adj=graph(A);cc=parts(adj,set())
        trial=[set()]+[{v} for v in sorted(A-{x,y}) if len(adj[v])>=3]
        for C in trial:
            groups=parts(adj,C);a=next(i for i,g in enumerate(groups) if x in g);b=next(i for i,g in enumerate(groups) if y in g)
            if a==b or len(groups)<=len(C)+1:continue
            if C&extras:continue
            rem=NB[m]&A-{x,y};assert rem=={blocker}
            decoys=rng.sample(sorted(A-extras-{x,y}-C),18);other=rng.sample(sorted(allnew-lost-NB[m]),28)
            c=dict(k=5,qs=[m],ends=[x,y],cut=sorted(C),remove=[blocker],added=[],drop=sorted(extras|set(decoys)),new=sorted(lost|set(other)))
            st,n,conf,out=solve(A,c,180000)
            if st=='FOUND':
                assert valid(out) and len(out)==191
                return dict(row=row,damaged=sorted(A),clean_majority=sorted(Astar),cut=sorted(C),ncomp=len(groups),joined_components=[a,b],mediator=m,case=c,swaps=len(A-set(out[::2])),witness=out)
            break
    raise RuntimeError('failed to produce a nontrivial positive repair')
if __name__=='__main__':print(json.dumps(control(),separators=(',',':')))
