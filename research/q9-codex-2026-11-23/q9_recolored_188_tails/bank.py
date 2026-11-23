from pathlib import Path
import random,itertools,json
d=Path(__file__).resolve().parent;r=d.parent
def valid(p):
    return len(p)==len(set(p)) and all(((a^b).bit_count()==1)==(j==i+1) for j,b in enumerate(p) for i,a in enumerate(p[:j]))
def ax(w):
    p=[0]
    for c in w:p.append(p[-1]^1<<c)
    return p
def trans(p):return ''.join(str((x^y).bit_length()-1) for x,y in zip(p,p[1:]))
def make_bank():
    bank=[list(map(int,w)) for w in (r/'q8_catalogue_96_98.words').read_text().split()]
    assert all(valid(ax(w)) for w in bank)
    rng=random.Random(78111);out={}
    for n in [188,190,191,192]:
        a=n//2;b=n-1-a
        def pieces(how,length):
            rows={}
            while len(rows)<how:
                i=rng.randrange(len(bank));w=bank[i];offset=rng.randrange(len(w)-length+1)
                perm=list(range(8));rng.shuffle(perm);rev=rng.randrange(2)
                text=w[offset:offset+length][::(-1 if rev else 1)];t=''.join(str(perm[c]) for c in text)
                pp=ax(map(int,t));mask=sum(1<<v for v in pp)
                rows[mask]=(mask,t,[i,offset,rev,perm])
            return list(rows.values())
        left=pieces(1300,a);right=pieces(1300,b);best=[]
        for m,t,j in left:
            k,v,u,jj=min(((m&v).bit_count(),v,u,jj) for v,u,jj in right)
            best.append((k,t[::-1]+'8'+u,j,jj))
        out[n]=[{'common':k,'word':w,'left':j,'right':jj} for k,w,j,jj in sorted(best)[:80]]
    (d/'q8_bank.json').write_text(json.dumps(out))
    print({n:(a[0]['common'],a[-1]['common']) for n,a in out.items()})
if __name__=='__main__':make_bank()
