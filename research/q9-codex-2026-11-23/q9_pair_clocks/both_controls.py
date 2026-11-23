from itertools import product
from search import D,axes,validate
from biends import lift
import random,json
rng=random.Random(810231);counts=[0,0]
for _ in range(230):
    groups=[(0,1),(2,3),(4,)];w=[rng.randrange(5) for _ in range(2*rng.randint(1,4))]
    choices=[next(g for g in groups if a in g) for a in w]
    def good(z):
        p=axes(z)
        if not validate(p):return False
        return any(validate([p[0]^1<<a]+p+[p[-1]^1<<b]) for a in range(5) for b in range(5))
    exp=any(good(z) for z in product(*choices));st,p,_=lift(w,groups[:2],4,40000)
    assert st!='UNKNOWN' and exp==(st=='FOUND');counts[exp]+=1
print(json.dumps(dict(small=counts)),flush=True)
out={}
for i,w in enumerate((D.parent/'q9_gap_generations/prior191.words').read_text().split()):
    p=axes(list(map(int,w)));assert validate(p)
    tips=[[bit for bit in range(9) if all((x^q[-1]^1<<bit).bit_count()>1 for x in q[:-1])] for q in [p,p[::-1]]]
    assert tips==[[],[]];out[i]=tips
    if i>=24:continue
    base=list(map(int,w[1:189]));assert len(base)==188
    ds=list(range(9));rng.shuffle(ds);ps=[tuple(ds[j:j+2]) for j in range(0,8,2)];s=ds[-1]
    for j,c in enumerate(base):
        if rng.randrange(6)==0:base[j]=rng.choice(next(g for g in [*ps,[s]] if c in g))
    st,q,_=lift(base,ps,s,120000)
    print(json.dumps(dict(case=i,status=st,edges=len(q)-1 if q else None,path=q)),flush=True)
print(json.dumps(dict(verified_bank=len(out),tips_checked=2*len(out),possible_extensions=0)),flush=True)
