from pathlib import Path
import random,gzip,json
D=Path(__file__).resolve().parent;R=D.parent;rng=random.Random(201963)
def path(w):
    v=[0]
    for k in w:v.append(v[-1]^1<<k)
    return v
def word(p):return [(u^v).bit_length()-1 for u,v in zip(p,p[1:])]
def valid(p):
    occ=set()
    for k,x in enumerate(p):
        if x in occ or sum(x^(1<<j) in occ for j in range(9))!=bool(k):return False
        occ.add(x)
    return True
def rigid(a,b):
    A=path(a);forbidden={v^d for v in A[1:] for d in [0]+[1<<k for k in range(9)]}
    def go(j,x,mp,avail):
        while j<len(b):
            ax=b[j]
            if ax not in mp:
                for d in avail:
                    y=x^1<<d
                    if y not in forbidden and go(j+1,y,{**mp,ax:d},avail-{d}):return True
                return False
            x^=1<<mp[ax]
            if x in forbidden:return False
            j+=1
        return True
    return go(0,0,{},set(range(9)))
def spoil(p,q):
    anchors=p[::2];other=set(q[2::2]);out=p[:]
    for i in range(1,len(p),2):
        u,z,v=p[i-1:i+2];y=u^z^v
        if sum((x^y).bit_count()==1 for x in anchors)!=2:continue
        if any((x^y).bit_count()==1 for x in other) or rng.random()<0.3:out[i]=y
    assert valid(out);return out
rows=[];tests=0
for k,l in enumerate(gzip.open(R/'q9_port_followup_public191.txt.gz','rt')):
    if len(rows)==32:break
    full=list(map(int,l.split()))
    for trial in range(3):
        if trial==1:full=full[::-1]
        a=[v^full[96] for v in full[:97][::-1]];b=[v^full[96] for v in full[96:191]]
        A=spoil(a,b);B=spoil(b,a);wa=word(A);wb=word(B);original=word(a);right=word(b)
        p=list(range(9));rng.shuffle(p);wb=[p[x] for x in wb];tests+=1
        if rigid(wa,wb):continue
        rows.append(dict(archive=k,trial=trial,l=wa,r=wb,changed_left=sum(x!=y for x,y in zip(a,A)),changed_right=sum(x!=y for x,y in zip(b,B)),scramble=p));break
(D/'controls.json').write_text(json.dumps(rows,separators=(',',':'))+'\n')
with (D/'controls.txt').open('w') as out:
    for z in rows:
        parts=[]
        for key in ('l','r'):
            w=z[key];parts.extend((1<<a)|(1<<b) for a,b in zip(w[::2],w[1::2]))
        print(*parts,file=out)
print('tested',tests,'strict_controls',len(rows))
