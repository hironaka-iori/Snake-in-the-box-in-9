from collections import Counter
import json,random
from prepare import D,R,CUBE,NB,components,ashex,unhex
rng=random.Random(8119572);bank={};sizes=Counter();seen=set();hist=Counter()
for l in (R/'q8_registered_donor_clusters.txt').open():
    _,i,*p=map(int,l.split());bank[i]=p
jobs={}
for l in (D/'cases.jsonl').open():
    c=json.loads(l);jobs.setdefault(c['line'],c)
for ln,l in enumerate((R/'q8_near_host_placements.log').open(),1):
    if not l.startswith('HOST '):continue
    _,a,b,t,k,perm=l.split()
    if int(k) not in (2,3):continue
    jobs.setdefault(ln,dict(line=ln,aid=int(a),bid=int(b),t=int(t),perm=perm,overlap=int(k)))
rows=list(jobs.values());rng.shuffle(rows)
with (D/'dispersed.jsonl').open('w') as dst:
    for c in rows:
        a=bank[c['aid']];pm=list(map(int,c['perm']));t=c['t']
        b=[256+(t^sum(1<<pm[d] for d in range(8) if v>>d&1)) for v in bank[c['bid']]]
        host=set(a+b);S=set(host);cross=sorted(set(a)&{v-256 for v in b});assert len(cross)==c['overlap']
        for v in cross:S.remove(v+256*rng.randrange(2))
        # Initial retained graph has no crossing edge, so all components are layer path intervals.
        desired=145+int(c['line']%2!=0)*9
        while len(S)>desired:
            runs=[]
            for p in (a,b):
                start=0
                while start<len(p):
                    if p[start] not in S:start+=1;continue
                    j=start+1
                    while j<len(p) and p[j] in S:j+=1
                    runs.append(p[start:j]);start=j
            runs.sort(key=len,reverse=True)
            g=rng.choice(runs[:min(5,len(runs))])
            v=rng.choice(g[max(0,len(g)//4):max(1,(3*len(g)+3)//4)]);S.remove(v)
        h=ashex(S)
        if h in seen:continue
        seen.add(h);groups=components(S)
        assert all(sum(len(NB[v]&S) for v in g)//2==len(g)-1 for g in groups)
        hist[max(map(len,groups))]+=1;sizes[len(S)]+=1
        print(json.dumps(dict(line=c['line'],aid=c['aid'],bid=c['bid'],perm=c['perm'],t=t,overlap=len(cross),anchors=len(S),rule='dispersed',components=len(groups),fixed=h,host=ashex(host)),separators=(',',':')),file=dst)
print(json.dumps(dict(selected_placements=len(rows),fixed_sets=len(seen),anchor_sizes=sizes,largest_component_sizes=hist),indent=2))
