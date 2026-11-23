from run import *
rng=random.Random(97141)
for p in bank:verify(p)
pairs=sorted((len(set(p)^set(q)),i,j) for i,p in enumerate(bank) for j,q in enumerate(bank[:i]) if set(p)!=set(q))
for distance,i,j in pairs[:80]:
    p,q=bank[i],bank[j];axes=sorted((len(split(p,a)^split(q,a)),a) for a in range(9) if split(p,a)!=split(q,a))
    if len(axes)<2:continue
    aa=[axes[0][1],axes[-1][1]]
    free=[(split(p,a)^split(q,a))|set(rng.sample(sorted(split(cube,a)),12)) for a in aa]
    hint=set(p)-set(rng.sample(p,30))
    result=solve(p,aa,free,192,18000,hint=hint)
    if result.get('status')=='FOUND':
        result.update(ref=i,other=j,axes=aa,old_distance=distance,released=list(map(sorted,free)),actual_delta=[len(split(p,a)^split(result['witness'],a)) for a in aa],outside_hint=len(set(result['witness'])-hint))
        print(json.dumps(result));break
else:raise RuntimeError('no positive')
