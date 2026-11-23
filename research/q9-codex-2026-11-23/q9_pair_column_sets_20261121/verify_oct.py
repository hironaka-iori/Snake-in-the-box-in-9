import json
from octagons import cycles
cs=cycles(tuple(range(2,9))); keys=set()
for c in cs:
    s={-v-1 for v in c};assert len(s)==8 and len({v&3 for v in s})==1
    nb={v:{t for t in s if (v^t).bit_count()==1} for v in s}
    assert all(len(t)==2 for t in nb.values())
    v=next(iter(s));queue=[v];seen={v}
    for v in queue:
        for w in nb[v]-seen:seen.add(w);queue.append(w)
    assert seen==s
    keys.add(tuple(sorted(s)))
assert len(cs)==len(keys)==26880
print(json.dumps(dict(unique_induced_8cycles=len(keys),axis_pair=[0,1],count_factors=[35,32,24])))
