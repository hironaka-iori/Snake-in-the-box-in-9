from pathlib import Path
import gzip,json,random,itertools
D=Path(__file__).resolve().parent;R=D.parent;rng=random.Random(2709115)
def verts(word):
    p=[0]
    for c in word:p.append(p[-1]^(1<<c))
    return p
def valid(p):
    old=set()
    for j,v in enumerate(p):
        if v in old or sum((v^(1<<k)) in old for k in range(10))!=(j>0):return False
        old.add(v)
    return True
public=[list(map(int,l.split())) for l in gzip.open(R/'q9_port_followup_public191.txt.gz','rt')]
out=[];checks=[]
for k,p in enumerate(public[:15]):
    w=[(x^y).bit_length()-1 for x,y in zip(p,p[1:])];splits=[w[:64],w[64:128],w[128:]]
    for trial in range(25000):
        axes=rng.sample(range(9),3);arms=[];maps=[]
        for t,(a,seg) in enumerate(zip(axes,splits)):
            pos=[i for i,x in enumerate(seg) if x==a]
            if len(pos)<3:break
            i=rng.randrange(len(pos)-2);at=pos[i:i+2];z=[9 if j in at else c for j,c in enumerate(seg)]
            # Distinct local coordinate names as well as different merged pairs.
            perm=list(range(10))
            if t==1:
                rare=sorted(range(9),key=lambda x:(z.count(x),rng.random()))[:3];u,v=rng.sample(rare,2);perm[u],perm[v]=perm[v],perm[u]
            arms.append([perm[x] for x in z]);maps.append([i if j!=9 else a for i,j in []] if False else dict(split_axis=a,perm=perm))
        if len(arms)!=3:continue
        raw=sum(arms,[]);q=verts(raw)
        if not valid(q):continue
        # Explicitly verify all uniform 10 -> 9 surjections fail on this full window.
        if any(valid(verts([b if c==a else c for c in raw])) for a in range(10) for b in range(a)):continue
        out.append(q);checks.append(dict(source=k,trial=trial,maps=maps));break
    else:raise ValueError(k)
(D/'positive.txt').write_text(''.join('10 '+' '.join(map(str,q))+'\n' for q in out));(D/'control_meta.json').write_text(json.dumps(checks,indent=2)+'\n')
if __name__=='__main__':print(len(out))
