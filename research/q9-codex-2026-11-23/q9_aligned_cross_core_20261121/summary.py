from collections import Counter
from pathlib import Path
import json
D=Path(__file__).resolve().parent;regions=(D/'cases.dat').read_text().splitlines()
checked={};summary={}
ids=list(map(int,(D/'small.ids').read_text().split()))
for file in ['core','release','core_retry','release_retry','small_all_released']:
    records=[]
    retries=[json.loads(l) for l in (D/(file+'_index.jsonl')).read_text().splitlines()] if file.endswith('_retry') else None
    for l in (D/(file+'.log')).read_text().splitlines():
        t=l.split()
        assert t[0]=='ROW'
        row,omit,nodes,leaves,graphs,low,dead,hcut,cut,w=map(int,t[1:])
        assert not w and graphs==low+dead+hcut
        if retries is not None:row,omit=retries[row]
        elif file=='small_all_released':row=ids[row]
        key=(row,omit);failed=bool(hcut or cut)
        checked[key]=checked.get(key,True) and failed
        records.append((nodes,leaves,graphs,low,dead,hcut,cut))
    if file=='small_all_released':
        assert len(records)==sum(int(regions[i].split()[1]) for i in ids)
    summary[file]=dict(jobs=len(records),**dict(zip(['nodes','leaves','hamilton_calls','initial_degree_pruned','hamilton_exhausted','hamilton_cutoff','combination_cutoff'],map(sum,zip(*records)))))
unresolved=[k for k,fail in checked.items() if fail]
print(json.dumps(dict(distinct_regions=len(regions),distinct_fixed_or_released_specs=len(checked),unresolved_specs=len(unresolved),unresolved=unresolved,solver=summary),indent=2))
