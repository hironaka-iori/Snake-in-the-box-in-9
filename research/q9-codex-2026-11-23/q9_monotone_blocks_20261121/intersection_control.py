from prepare import *
ds=[(130,17,186,(6,7,8),0),(119,9,178,(5,7,8),0),(4,20,189,(6,7,8),0)]
r=random.Random(51105);bank=(root/'q9_gap_generations/prior191.words').read_text().split();meta=[]
with (D/'intersects_control.in').open('w') as f:
    for i,lo,hi,ax,pattern in ds:
        p=path(bank[i])[lo:hi];a,b,c=ax;pm=[r.sample(range(7),7) for t in range(4)];off=[r.randrange(128) for t in range(4)];lab=[]
        for x in p:
            side=x>>a&1
            if side==0:
                options=[k for k,d in enumerate([b,c]) if x>>d&1]
                assert options
                z=r.choice(options);sec=[b,c][z];g=z
            else:sec=b;g=2+(x>>b&1)
            ids=[d for d in range(9) if d not in (a,sec)]
            u=off[g]^sum(((x>>d)&1)<<pm[g][j] for j,d in enumerate(ids));lab.append(put(g,u,7,8))
        print(i,7,8,*lab,file=f);meta.append(dict(id=i,lo=lo,hi=hi,axes=ax,pm=pm,off=off))
(D/'intersects_control.json').write_text(json.dumps(meta)+'\n')
