import itertools,json
from collections import Counter,defaultdict
from prepare import D,R,walk,canon,valid
def components(S):
    s=set(S);out=[]
    while s:
        q=[s.pop()]
        for v in q:
            nb={v^1<<k for k in range(9)}&s;q.extend(nb);s-=nb
        out.append(set(q))
    return sorted(out,key=len,reverse=True)
def order(c):
    def ns(x):return {x^1<<k for k in range(9)}&c
    e,=sorted(x for x in c if len(ns(x))==1)[:1]
    p=[e]
    while len(p)<len(c):p.append(next(iter(ns(p[-1])-set(p[-2:]))))
    return p
def name(p):return ''.join(str((x^y).bit_length()-1) for x,y in zip(p,p[1:]))
cs=list(map(json.loads,(D/'cases.jsonl').read_text().splitlines()))
hashes=defaultdict(list)
for i,c in enumerate(cs):hashes[c['w']].append(i)
out=[]; census=Counter()
for r,w in enumerate((R/'q9_gap_generations/prior191.words').read_text().split()):
    P=walk(w)
    for d in range(9):
        for val in range(2):
            S={v for v in P if (v>>d)&1==val};cc=components(S)
            if len(cc)!=2 or len(cc[1])!=2:continue
            long=order(cc[0]);ww=name(long);census[len(ww)]+=1
            can=canon(ww)
            for i in hashes.get(can,[]):
                c=cs[i];z=c['lo']
                for old in (long,long[::-1]):
                    mp={int(a):int(b) for a,b in zip(name(old),c['w'])}
                    if canon(name(old))!=can or len(set(mp.values()))!=8 or len(mp)!=8:continue
                    mp[d]=8
                    def apply(x):return sum(1<<k for j,k in mp.items() if x>>j&1)
                    trans=apply(old[0]); Q=[apply(x)^trans for x in P]
                    if set(Q)&set(range(256))!=set(z+c['edge']):continue
                    assert valid(Q);cross=sum(a^b==256 for a,b in zip(Q,Q[1:]));out.append(dict(case=i,row=r,cross=cross,vertices=Q))
(D/'archive_controls.jsonl').write_text(''.join(json.dumps(v,separators=(',',':'))+'\n' for v in out))
print('possible_lower_lengths',sorted(census.items()),'aligned',len(out),'shape',Counter((len(cs[v['case']]['w']),v['cross']) for v in out))
