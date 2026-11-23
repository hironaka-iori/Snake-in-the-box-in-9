import gzip,json,random
from search import D,R,P,shade,solve,validate
rng=random.Random(331907);known=[list(map(int,l.split())) for l in gzip.open(R/'q9_port_followup_public191.txt.gz','rt')];rows=[]
for i in range(15):
    p=shade(known[(11*i+3)%len(known)]);ground=set(p[::2]);missing=rng.choice(sorted(ground));s=ground-{missing}
    gone=rng.sample(sorted(s),2+i%4);new=rng.sample(sorted(set(P)-ground),len(gone));s.difference_update(gone);s.update(new)
    area=set(gone+new+rng.sample(sorted(set(P)-{missing}),24));area.discard(missing)
    r=solve(s,0,[],len(gone),20000,0,i,None,100,True,cloud=area)
    assert r['status']=='FOUND' and len(r['path'])==191 and validate(r['path']);rows.append(r)
(D/'region_control.json').write_text(json.dumps(rows,separators=(',',':'))+'\n');print(len(rows))
