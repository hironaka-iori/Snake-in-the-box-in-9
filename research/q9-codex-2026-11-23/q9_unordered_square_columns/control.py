from data import *
from model import solve
from random import Random
rng=Random(38711)
def enumerate_paths(dim):
    result=[]
    def dfs(p,forbid):
        if len(p)>=2:result.append(p[:])
        new=forbid|{p[-1]}|{p[-1]^1<<a for a in range(dim)}
        for a in range(dim):
            v=p[-1]^1<<a
            if v not in forbid:dfs(p+[v],new)
    for x in range(1<<dim):dfs([x],{x})
    return result
for dim in (3,4):
    bank=enumerate_paths(dim);known={(len(p)-1,tuple(hist(p,dim))) for p in bank};cases=[0,0]
    for i in range(220):
        p=rng.choice(bank);h=hist(p,dim)
        if i%3==0:
            c=rng.randrange(len(h));h[c]=rng.randint(0,4)
        length=rng.randrange(max(1,len(p)-3),min((1<<dim)-1,len(p)+3)+1);lost=rng.randrange(3)
        down=set(rng.sample(range(len(h)),rng.randrange(len(h)+1)));up=set(rng.sample(range(len(h)),rng.randrange(len(h)+1)))
        wanted=any(n==length and sum(max(0,a-b) for a,b in zip(h,H))==lost and all((a>=b or j in up) and (a<=b or j in down) for j,(a,b) in enumerate(zip(h,H))) for n,H in known)
        z=solve(h,length,lost,down,up,dim=dim,budget=20000)
        assert z['status'] not in ('UNKNOWN','CUT_LIMIT') and (z['status']=='FOUND')==wanted,(dim,h,length,lost,down,up,z['status'],wanted)
        if wanted:check(z['path'],dim)
        cases[wanted]+=1
    print(json.dumps(dict(dim=dim,cases=cases)),flush=True)
b=json.loads((D/'inputs.json').read_text())['public']
for j in range(24):
    a,bits=rng.sample(range(9),2);p=permute(b[j],sorted((a,bits)));h=hist(p);hint=[]
    for i,k in enumerate(h):hint.extend(4*i+x for x in rng.sample(range(4),k))
    if j%3==0:
        z=solve(h,191,0,hint=hint,budget=16000);h0=h
    else:
        h0=h[:];sel=rng.choice([i for i,n in enumerate(h) if n>=1]);h0[sel]-=1
        if j%3==2:
            add=rng.choice([i for i,n in enumerate(h) if n<3 and i!=sel]);h0[add]+=1
        z=solve(h0,191,int(j%3==2),{add} if j%3==2 else set(),{sel},hint=hint,budget=16000)
    print(json.dumps(dict(id=j,axes=sorted((a,bits)),h=h0,randomized_hint=hint,result=z)),flush=True)
