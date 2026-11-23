from prep import D,R,project,points
import sys,random,json
sys.path.insert(0,str(R))
from search_q9_unordered_projection import solve
from itertools import product
from random import Random

def verify(p,n,S):
    return len(p)>=n+1 and len(set(p))==len(p) and all(0<=u<512 for u in p) and {u&255 for u in p}==S and all(((v^u).bit_count()==1)==(i+1==j) for j,v in enumerate(p) for i,u in enumerate(p[:j]))

def back(basis):
    a=[0]
    for u in basis:a += [x^u for x in a]
    assert len(set(a))==256
    return {v:i for i,v in enumerate(a)}

def control():
    from subprocess import run
    rng=Random(7742);bank=(R/'q9_gap_generations/prior191.words').read_text().split()
    for i,w in enumerate(bank[:16]):
        s=rng.randrange(9);real=points(w);native={project(x,s) for x in real}
        ds=list(range(8));rng.shuffle(ds);a,b=ds[:2];basis=[1<<j for j in range(8)]
        extra=(1<<b) if i%2==0 else (1<<b)|(1<<ds[2]);basis[a]^=extra
        perm=[0]
        for g in basis:perm += [x^g for x in perm]
        raw={perm[x] for x in native}
        log=run([str(D/'screen'),'191','1','0'],input=' '.join(map(str,raw))+'\n',capture_output=True,text=True,check=True).stdout
        hits=[l for l in log.splitlines() if l.startswith('CASE') and set(map(int,l.split()[2:10]))==set(basis)]
        assert hits
        g=list(map(int,hits[0].split()[2:10]));inv=back(g);target={inv[x] for x in raw}
        hint={inv[perm[project(x,s)]]+256*((x>>s)&1) for x in real}
        st,p=solve(hint,191,90000);assert not p or verify(p,191,target)
        print(json.dumps(dict(row=i,retained_hidden_basis=True,status=st,path=p)),flush=True)

def main(n,src,limit,cap):
    rows=[l.split() for l in (D/src).read_text().splitlines() if l.startswith('CASE')]
    rng=Random(91397+n);rng.shuffle(rows);seen=set()
    for v in rows:
        source=int(v[1]);g=list(map(int,v[2:10]));inv=back(g);s=frozenset(inv[int(x)] for x in v[11:])
        if s in seen:continue
        seen.add(s);st,p=solve(s,n,cap);assert not p or verify(p,n,s)
        print(json.dumps(dict(row=source,basis=g,goal=n,status=st,path=p)),flush=True)
        if p or len(seen)>=limit:break
if __name__=='__main__':
    if sys.argv[1]=='control':control()
    else:main(int(sys.argv[1]),sys.argv[2],int(sys.argv[3]),int(sys.argv[4]))
