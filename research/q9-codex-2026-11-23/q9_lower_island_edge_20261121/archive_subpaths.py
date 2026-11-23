import json,itertools
from collections import defaultdict,Counter
from prepare import D,R,canon,walk,valid
cs=list(map(json.loads,(D/'cases.jsonl').read_text().splitlines()));cases=defaultdict(list)
for j,c in enumerate(cs):cases[c['w']].append(j)
hits=[];catalogue=(R/'q9_gap_generations/prior191.words').read_text().split()
for row,w in enumerate(catalogue):
    P=walk(w)
    for rev in (False,True):
        seq=P[::-1] if rev else P
        for dr in range(9):
            batches=[list(it) for _,it in itertools.groupby(seq,key=lambda v:v>>dr&1)]
            for k in range(len(batches)-3):
                free,long,bridge,island=batches[k:k+4]
                if len(island)<2 or not 94<=len(long)<=96:continue
                candidate=free+long+bridge+island[:2]
                def asword(p):return ''.join(str((x^y).bit_length()-1) for x,y in zip(p,p[1:]))
                key=canon(asword(long))
                for j in cases.get(key,[]):
                    c=cs[j]
                    for order in (long,long[::-1]):
                        mp={int(x):int(y) for x,y in zip(asword(order),key)}
                        if len(mp)!=8 or len(set(mp.values()))!=8:continue
                        mp[dr]=8
                        def trans(x):return sum(1<<v for k,v in mp.items() if x>>k&1)
                        t=trans(order[0]);p=[trans(x)^t for x in candidate]
                        if {x for x in p if x<256} != set(c['lo']+c['edge']):continue
                        assert valid(p) and sum((x^y)==256 for x,y in zip(p,p[1:]))==3
                        hits.append(dict(case=j,row=row,edges=len(p)-1,vertices=p))
(D/'archive_three.jsonl').write_text(''.join(json.dumps(z,separators=(',',':'))+'\n' for z in hits))
print('hits',len(hits),'edges',sorted(Counter(z['edges'] for z in hits).items()),'classes',len({canon(''.join(str((x^y).bit_length()-1) for x,y in zip(z['vertices'],z['vertices'][1:]))) for z in hits}))
