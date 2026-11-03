"""Try to falsify the six-count sum hypothesis using complete saved snakes."""
from pathlib import Path
from itertools import combinations
import hashlib,json
H=Path(__file__).resolve().parents[1];R=H.parents[1]
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
sources=[R/'work/bank9.json',R/'milestones/121-replacement-window-pressure/data/boundary-paths.json']
bank=json.loads(sources[0].read_text(encoding='utf-8-sig'))
rows=[dict(label='bank'+str(i),order=p['vertex_sequence']) for i,p in enumerate(bank)]
rows += [dict(label='boundary'+p['label'],order=p['order']) for p in json.loads(sources[1].read_text())['paths']]
def canon(ds):
    d={};return tuple(d.setdefault(x,len(d)) for x in ds)
mins={};matches=0;pairs=0
for p in rows:
    vs=p['order'];S=set(vs);assert len(vs)==len(S) and all(0<=v<512 for v in vs)
    ds=[]
    for i,u in enumerate(vs):
        for j in range(i+1,len(vs)):
            assert ((u^vs[j]).bit_count()==1)==(j==i+1);pairs+=1
        if i+1<len(vs):ds.append((u^vs[i+1]).bit_length()-1)
    counts=[sum(all(z not in S for z in (v^(1<<a),v^(1<<b),v^(1<<a)^(1<<b)))
        for a,b in combinations(range(9),2)) for v in vs]
    for r in range(len(ds)-6):
        word=canon(ds[r:r+7]);key=min(word,canon(ds[r:r+7][::-1]));cs=counts[r+1:r+7];total=sum(cs)
        row=dict(label=p['label'],start=r,directions=ds[r:r+7],canonical=list(key),counts=cs,total=total)
        if key not in mins or total<mins[key]['total']:mins[key]=row
        if key==(0,1,2,3,0,4,2):matches+=1
out=dict(status='PASS_SAVED_SNAKES_AND_SIX_COUNT_SCAN',paths=len(rows),pairs_checked=pairs,
    case10_occurrences=matches,case10_minimum=mins.get((0,1,2,3,0,4,2)),global_minimum=min(mins.values(),key=lambda x:x['total']),
    by_shape=sorted(mins.values(),key=lambda x:(x['total'],x['canonical'])),
    source_pins={p.relative_to(R).as_posix():sha(p) for p in sources},script_sha256=sha(Path(__file__)),
    scope='Finite saved-snake evidence only. Absence of a counterexample does not prove a universal sum bound.')
p=H/'data/six-sum-bank.json';assert not p.exists();p.write_text(json.dumps(out,indent=2)+'\n')
print('paths',len(rows),'case10 occurrences',matches,'case10 minimum',out['case10_minimum'],'global',out['global_minimum'],flush=True)
