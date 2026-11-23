"""Release all columns on one side plus two independent patches on its complement."""
import gzip,json,random,sys
from search_q9_flexible_columns import complete,face
from search_q9_unordered_projection import project
f=sys.argv[1];budget=int(sys.argv[3]);rng=random.Random(14829)
reader=gzip.open if f.endswith('.gz') else open
with reader(f,'rt') as fp:bank=[list(map(int,l.split())) for l in fp]
p=json.load(open('q9_explicit_q8_96_plus_94.json'))['vertices']
h=project(p,8);S={x%256 for x in h};P={v for v in range(256) if v.bit_count()%2}|face(15,0)
st,w=complete(h,S^set(sorted(P)[:4]),P,191,40000,4,S-P,propagate=True)
assert st=='FOUND';print(json.dumps(['control',st,w]),flush=True)
jobs=[(i,d,c) for i in range(len(bank)) for d in range(9) for c in (0,1)];rng.shuffle(jobs)
for i,d,c in jobs[:int(sys.argv[2])]:
    h=project(bank[i],d);S={x%256 for x in h}
    other={v for v in range(256) if v.bit_count()%2!=c};extra=set()
    for j in range(2):
        mask=sum(1<<k for k in rng.sample(range(8),3));extra|=face(mask,rng.randrange(256)&~mask)-other
    P=extra|other
    st,w=complete(h,S,P,192,budget,0,S-P,propagate=True)
    print(json.dumps([i,d,c,format(sum(1<<v for v in extra),'x'),st,w],separators=(',',':')),flush=True)
    if w:break
