from pathlib import Path
from collections import Counter
import json,sys
from itertools import chain
D=Path(__file__).resolve().parent;R=D.parent;sys.path.insert(0,str(R/'q9_internal_xor_20261121'))
from verify import vertices,quadratic,wfrom
N=[{v^1<<d for d in range(9)} for v in range(512)]
seen=set();raw=Counter()
recorded=set()
for l in chain.from_iterable((D/name).open() for name in (sys.argv[1:] or ['archive.log'])):
    if not l.startswith('SET '):continue
    mask=tuple(int(t) for t in l.split()[1:])
    if mask in recorded:continue
    recorded.add(mask)
    s={64*j+k for j,m in enumerate(mask) for k in range(64) if m>>k&1}
    assert len(s)==193
    comps=[]
    while s:
        v=next(v for v in s if len(N[v]&s)<=1);path=[v];s.remove(v)
        while choices:=N[path[-1]]&s:
            assert len(choices)==1
            v=choices.pop();s.remove(v);path.append(v)
        assert not quadratic(path)
        comps.append(path)
    assert len(comps)==2
    # Independently check absence of cross-edges after extracting the two components.
    other=set(comps[1]); assert all(not (N[v]&other) for v in comps[0])
    f=tuple(sorted((wfrom(a) or '-' for a in comps),key=lambda w:(-len(w),w)))
    raw[min(len(a) for a in comps)]+=1
    if f in seen:continue
    seen.add(f);print(*f)
print(json.dumps(dict(distinct_component_shape_pairs=len(seen),archived_by_smaller_vertex_count=raw)),file=sys.stderr)
