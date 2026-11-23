from enhanced import *
i,j=1,0
p,q=bank[i],bank[j];aa=[1,8];o=[split(p,a) for a in aa];qcols=[split(q,a) for a in aa]
u=[split(cube,a)-(c&other) for a,c,other in zip(aa,o,qcols)]
hint=set(q)-set(random.Random(135251).sample(q,11))
res=solve(p,aa,u,192,80000,hint=hint)
assert res['status']=='FOUND' and res['fixed']==0 and res['pool']==512
res.update(source=i,donor=j,axes=aa,mandatory=[sorted(c-v) for c,v in zip(o,u)],newcols=[len(split(res['witness'],a)^c) for a,c in zip(aa,o)],outside_hint=len(set(res['witness'])-hint))
print(json.dumps(res))
