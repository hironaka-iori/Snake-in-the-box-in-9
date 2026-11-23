from collections import Counter
from itertools import accumulate
from operator import xor
import json
from run import ROOT,HERE,inspect,regions

walks={}
domains={}
row_ids={}
for i,line in enumerate(open(ROOT/'q9_new189_nearmisses.words')):
    label,word=line.split()
    if label!='2':continue
    p=list(accumulate([1<<int(d) for d in word],xor,initial=0))
    walks[i]=p
    chords=inspect(p)
    assert len(chords)==2
    for fixed,params in regions(p,chords):
        key=(i,str(params))
        row_ids[key]=fixed
        domains.setdefault(fixed,key)
statuses={}
for file in ['results','minicard_all']:
    data=[json.loads(l) for l in open(HERE/(file+'.jsonl'))]
    control=data[0].get('control')
    if control:
        p=control['witness']
        assert len(p)>=192 and not inspect(p)
    assert 'counts' in data[-1]
    jobs=[x for x in data if 'status' in x]
    a={row_ids[x['row'],str(x['params'])]:x['status'] for x in jobs}
    assert set(a)==set(domains)
    assert Counter(a.values())==data[-1]['counts']
    statuses[file]=a
pairs=Counter((statuses['results'][s],statuses['minicard_all'][s]) for s in domains)
excluded={s for s in domains if 'UNSAT' in (statuses['results'][s],statuses['minicard_all'][s])}
unknown=set(domains)-excluded
assert all(statuses[f][s]=='UNKNOWN' for f in statuses for s in unknown)
bit=lambda s: sum(1<<v for v in s)
bits=[bit(s) for s in excluded]
implied=sum(any(t&bit(s)==t for t in bits) for s in unknown)
print(json.dumps(dict(inputs=len(walks),templates=len(row_ids),distinct=len(domains),statuses={k:dict(Counter(v.values())) for k,v in statuses.items()},paired={','.join(k):v for k,v in pairs.items()},distinct_excluded=len(excluded),implied_by_subset=implied,still_unknown=len(unknown)-implied,anchors=[min(map(len,domains)),max(map(len,domains))]),indent=2))
