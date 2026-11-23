import json,sys,random
from collections import defaultdict
from prepare import D,R,words,majority,NB
from solve import solve
rng=random.Random(611073);jobs=list(map(json.loads,(D/'jobs.jsonl').read_text().splitlines()))
if sys.argv[1]=='narrow':
    initial={r[0]:r[1] for f in D.glob('run*.jsonl') for r in map(json.loads,f.read_text().splitlines())}
    for i,c in enumerate(jobs):
        if initial[i]!='UNKNOWN':continue
        st,cut,conf,w=solve(majority(words[c['row']]),c,100000)
        print(json.dumps([i,st,cut,conf,w],separators=(',',':')),flush=True)
        if w:break
else:
    broad=[];used=set()
    for i,c in enumerate(jobs):
        if c['row'] in used or c['kind'] not in ('via','double') or c['k']!=8:continue
        if rng.random()<.6:continue
        A=majority(words[c['row']]);fixed=set(c['cut'])|set(c['ends']);med=set(c['qs']);added=set(c['added'])
        ban=set.union(*(NB[q] for q in med))-fixed-added
        rest=sorted(A-set(c['drop'])-fixed);rng.shuffle(rest);push=len(broad)%4==0
        drop=sorted(A-fixed) if push else sorted(set(c['drop'])|set(rest[:24]))
        new=sorted(x for x in range(512) if x.bit_count()%2==0 and x not in A|ban)
        broad.append((i,{**c,'drop':drop,'new':new,'k':9 if push else 7}))
        used.add(c['row'])
    (D/'broadfamilies.jsonl').write_text(''.join(json.dumps([i,c],separators=(',',':'))+'\n' for i,c in broad))
    for j,(i,c) in enumerate(broad):
        st,cut,conf,w=solve(majority(words[c['row']]),c,4500)
        print(json.dumps([j,i,st,cut,conf,w],separators=(',',':')),flush=True)
        if w:break
