from pathlib import Path
import json
d=Path(__file__).parent
adj=[sum(1<<(a^(1<<i)) for i in range(9)) for a in range(512)]
steps=[[a^((1<<i)|(1<<j)) for i in range(9) for j in range(i)] for a in range(512)]
def ports(a,b):
    return [a^(1<<i) for i in range(9) if (a^b)>>i&1]
def alive(p,occ):
    return any((adj[o]&occ).bit_count()==2 for o in p)
def check(wings,tips,seq,occ,required,gone):
    if not wings:
        if any((v&~occ)==0 for v in gone):return False
        if not tips:return True
        return all(any((adj[q^(1<<i)]&occ).bit_count()==1 for i in range(9)) for q in [seq[0],seq[-1]])
    (l,r,k),*other=wings
    def walk(u,dest,remaining,current,edges,chain):
        if not remaining:
            if dest is not None:
                if (u^dest).bit_count()!=2:return False
                opt=ports(u,dest)
                if not alive(opt,current):return False
                edges=edges+[opt]
            s=seq.copy()
            if l==0:s[0]=u
            if r==len(seq)-1:s[-1]=u
            return check(other,tips,s,current,edges,gone)
        for v in steps[u]:
            if current>>v&1:continue
            if dest is not None and (v^dest).bit_count()>2*remaining:continue
            val=current|1<<v;new=edges+[ports(u,v)]
            if all(alive(pair,val) for pair in new) and walk(v,dest,remaining-1,val,new,chain+[v]):return True
        return False
    if l==0:return walk(seq[r+1],None,k,occ,required,[])
    return walk(seq[l-1],seq[r+1] if r<len(seq)-1 else None,k,occ,required,[])
tallies={0:[0,0,0],2:[0,0,0]}
for line in (d/'inputs.txt').open():
    ty,id,n,*p=map(int,line.split())
    if ty:continue
    seq=p[::2];m=len(seq)//2
    mask=sum(1<<v for v in seq)
    orig=[ports(a,b) for a,b in zip(seq,seq[1:])]
    for la in (1,2):
      for lb in (1,2):
       for l in range(m-la+1):
        for r in range(m+1,len(seq)-lb+1):
            a,b=l+la-1,r+lb-1
            gone=[sum(1<<v for v in seq[l:a+1]),sum(1<<v for v in seq[r:b+1])]
            occ=mask^gone[0]^gone[1];edges=orig[:max(0,l-1)]+orig[a+1:r-1]+orig[b+1:]
            good=all(alive(q,occ) for q in edges)
            for tips,row in tallies.items():
                missing=la+lb-tips//2
                row[0]+=missing+1
                if good:
                    row[1]+=missing+1
                    for x in range(missing+1):
                        row[2]+=check([(l,a,x),(r,b,missing-x)],tips,seq,occ,edges,gone)
for tips,row in tallies.items():
    fn='exact7o.log' if tips else 'exact7e.log'
    t=(d/fn).read_text().splitlines()[-1].split()
    assert list(map(int,[t[2],t[3],t[-1]]))==row
print(json.dumps(tallies))
