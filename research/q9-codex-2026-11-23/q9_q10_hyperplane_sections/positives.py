from pathlib import Path
from random import Random
import json
from census import section
D=Path(__file__).resolve().parent;R=D.parent
def check(p,dimension):
    assert len(set(p))==len(p) and all(0<=x<1<<dimension for x in p)
    assert all(((x^y).bit_count()==1)==(j==k+1) for j,y in enumerate(p) for k,x in enumerate(p[:j]))
def make():
    rng=Random(649713);bank=(R/'q9_gap_generations/prior191.words').read_text().split();data=[]
    for r in range(16):
        w=bank[r];q=[0]
        for x in w:q.append(q[-1]^1<<int(x))
        gaps=r%4+1;positions=[]
        for j in range(gaps):
            start=10+42*j+rng.randrange(10);length=rng.choice((1,2));positions.append((start,start+length-1))
        p=[];up=False
        for t,x in enumerate(q):
            if any(t==a-1 for a,b in positions):p.extend([x,x^512]);up=True
            elif any(t==b+1 for a,b in positions):p.extend([x^512,x]);up=False
            else:p.append(x^(512 if up else 0))
        check(p,10);bs=list(range(10));rng.shuffle(bs);shift=rng.randrange(1024)
        def transform(x):return shift^sum(((x>>j)&1)<<bs[j] for j in range(10))
        p=[transform(x) for x in p];check(p,10);m=1<<bs[9];b=(m&shift).bit_count()%2;values=section(p,m,b)
        assert len(values)==192-sum(k-j+1 for j,k in positions)
        # A full-rank internal reparametrization of all physical section labels.
        # Although the section calculation is untouched, this makes using the identity basis fail.
        gl=[1<<j for j in range(9)]
        for _ in range(32):
            x,y=rng.sample(range(9),2);gl[x]^=gl[y]
        mapped=[]
        for v in values:
            x=0
            for j in range(9):
                if v>>j&1:x^=gl[j]
            mapped.append(x)
        aux={'mother':p,'mask':m,'side':b,'axis_chart':gl,'mandatory':mapped,'source':r,'gaps':positions}
        data.append(aux)
    (D/'positive.json').write_text(json.dumps(data,separators=(',',':'))+'\n')
    with (D/'positive.in').open('w') as f:
        for j,row in enumerate(data):
            a=row['mandatory'];print(j,row['mask'],row['side'],len(a),*a,file=f)
if __name__=='__main__':make()
