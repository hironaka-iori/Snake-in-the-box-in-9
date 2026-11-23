from prepare import D,root,path,put
import random,json
r=random.Random(19604)
rows=(root/'q9_gap_generations/prior191.words').read_text().split()
ms=[]
with (D/'adaptive_control.in').open('w') as f:
    for i in r.sample(range(len(rows)),18):
        p=path(rows[i]);principal,axis0,axis1=r.sample(range(9),3)
        q=[];layout=r.sample(range(4),4);ps=[r.sample(range(7),7) for _ in layout];sh=[r.randrange(128) for _ in layout]
        for v in p:
            side=v>>principal&1;second=axis1 if side else axis0;label=side*2+(v>>second&1)
            ds=[k for k in range(9) if k not in (principal,second)]
            xi=sh[label]^sum((v>>d&1)<<ps[label][j] for j,d in enumerate(ds))
            q.append(put(layout[label],xi,7,8))
        print(i,7,8,*q,file=f);ms.append(dict(id=i,principal=principal,second=[axis0,axis1],layout=layout,pm=ps,translation=sh))
(D/'adaptive_control.json').write_text(json.dumps(ms)+'\n')
