from bank import *
from solver import solve
rng=random.Random(881341);stats=[0,0]
for i in range(200):
    word=[rng.randrange(5) for _ in range(rng.randint(4,10))];l,h=[(2,2),(3,2),(4,1),(4,2),(3,3),(4,4)][i%6]
    pairs=[(0,3),(1,4)];s=2
    dom=[range(5)]*l+[next((p for p in pairs if c in p),(s,)) for c in word]+[range(5)]*h
    def walk(path,legal,i):
        if i==len(dom):return True
        for c in dom[i]:
            x=path[-1]^1<<c
            if x in legal:continue
            forbidden=legal | {path[-1]} | {path[-1]^1<<k for k in range(5)}
            if walk(path+[x],forbidden,i+1):return True
        return False
    oracle=walk([0],{0},0);st,p,k=solve(word,pairs,s,l,h,100000)
    assert st!='UNKNOWN' and oracle==(st=='FOUND')
    if p:assert valid(p)
    stats[oracle]+=1
print(json.dumps(dict(small=stats)),flush=True)
real=(r/'q9_gap_generations/prior191.words').read_text().split()
for i in range(24):
    dims=list(range(9));rng.shuffle(dims);pairs=[tuple(dims[j:j+2]) for j in range(0,8,2)];s=dims[-1];l,h=[(1,2),(2,1),(2,2),(3,4),(4,4),(4,3)][i%6]
    w=list(map(int,real[i+32][l:-h]));change={x:a^b^x for a,b in pairs for x in (a,b)}
    w=[change.get(x,x) if rng.randrange(3)==0 else x for x in w];assert not valid(ax(w))
    st,p,k=solve(w,pairs,s,l,h,70000)
    print(json.dumps(dict(id=i,w=w,ps=pairs,s=s,l=l,r=h,status=st,path=p,conflicts=k)),flush=True)
