import itertools, json, random, sys
from collections import defaultdict
from pathlib import Path
d=Path(__file__).resolve().parent
r=d.parent
ar=(r/'q9_gap_generations/prior191.words').read_text().split()
f=json.loads((r/'q9_frequent_95_audit.json').read_text())
g=json.loads((r/'q9_record_facet_window_classes.json').read_text())
ids=sorted(set(range(len(ar)))-set(f['record_ids']).union(*g['donor_record_ids'].values()))
assert len(ids)==22
def path(w):
    p=[0]
    for c in w:p.append(p[-1]^1<<int(c))
    return p
def sig(w):
    return bytes(w.index(c) for c in w)
def transform(p,m,t):
    return [sum(1<<m[j] for j in range(9) if x>>j&1)^t for x in p]
def cases():
    rng=random.Random(297694);n=12
    for a,b in itertools.combinations(ids,2):
        w,v=ar[a],ar[b];P,Q=path(w),path(v)
        by=defaultdict(list)
        for j in range(192-n):
            for sign,u in [(1,v[j:j+n]),(-1,v[j:j+n][::-1])]:
                by[sig(u)].append((j+(n if sign<0 else 0),u))
        opts=[(i,j,u) for i in range(192-n) for j,u in by[sig(w[i:i+n])]]
        rng.shuffle(opts);transforms={};A=set(P)
        for i,j,u in opts[:550]:
            m=dict(zip(map(int,u),map(int,w[i:i+n])));lo=sorted(set(range(9))-set(m));hi=sorted(set(range(9))-set(m.values()));rng.shuffle(hi);m.update(zip(lo,hi));m=tuple(m[k] for k in range(9))
            t=P[i]^transform([Q[j]],m,0)[0]
            if (m,t) in transforms:continue
            T=transform(Q,m,t);cm=len(A&set(T))
            if 24<=cm<192:transforms[m,t]=cm
        # Retain some tightly aligned and some geometrically dissimilar poses for each donor pair.
        ordered=sorted(transforms,key=lambda k:-transforms[k])
        pool=ordered[:5]
        for lo,hi in [(145,191),(95,144),(50,94),(24,49)]:
            band=[k for k in ordered if lo<=transforms[k]<=hi and k not in pool];rng.shuffle(band);pool+=band[:4]
        for m,t in pool:
            T=transform(Q,m,t)
            yield a,b,m,t,transforms[m,t],P,T
print('IDS',ids,file=sys.stderr)
with (d/'poses.dat').open('w') as data,(d/'poses.jsonl').open('w') as meta:
    for a,b,m,t,cm,P,Q in cases():
        print(*P,*Q,file=data)
        print(json.dumps(dict(a=a,b=b,m=m,t=t,overlap=cm),separators=(',',':')),file=meta)
