from bank import *
from solver import solve
from itertools import product
rng=random.Random(984);stats=[0,0]
for i in range(150):
    ps=[(0,1)];s=2;n=rng.randrange(1,8);w=[rng.randrange(3) for j in range(n)];l,rh=rng.choice([(1,2),(2,2),(2,3),(1,1),(0,2)])
    def brute():
        # Ordinary 3-cube DFS, one physical direction at a time.
        dom=[range(3)]*l+[[0,1] if c in (0,1) else [2] for c in w]+[range(3)]*rh
        def dfs(p,i):
            if i==len(dom):return True
            for c in dom[i]:
                v=p[-1]^1<<c
                if v in p or any((v^u).bit_count()==1 for u in p[:-1]):continue
                if dfs(p+[v],i+1):return True
            return False
        return dfs([0],0)
    expected=brute();st,p,k=solve(w,ps,s,l,rh,10000)
    assert st!='UNKNOWN' and (st=='FOUND')==expected
    if p:assert valid(p)
    stats[expected]+=1
print(json.dumps(dict(small=stats)),flush=True)
real=(d.parent/'q9_gap_generations/prior191.words').read_text().split()
for i in range(16):
    word=list(map(int,real[i]));l,rh=[(2,2),(2,3),(3,2),(1,3)][i%4];core=word[l:-rh]
    perm=list(range(9));rng.shuffle(perm);ps=[tuple(perm[j:j+2]) for j in range(0,8,2)];ss=perm[-1];swap={c:a^b^c for a,b in ps for c in (a,b)}
    scrambled=[swap.get(c,c) if rng.randrange(3)==0 else c for c in core]
    assert not valid(ax(scrambled))
    st,p,k=solve(scrambled,ps,ss,l,rh,20000)
    print(json.dumps(dict(id=i,w=scrambled,ps=ps,s=ss,l=l,r=rh,status=st,path=p,conflicts=k)),flush=True)
