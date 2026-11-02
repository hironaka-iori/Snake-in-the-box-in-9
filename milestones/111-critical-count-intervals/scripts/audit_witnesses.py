"""Independently check selected local vertex sets; no full-snake claim."""
from pathlib import Path
from itertools import combinations
import hashlib,json
HERE=Path(__file__).resolve().parents[1]
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest();rows=[]
for path in sorted((HERE/'data/probes').glob('*.json')):
    d=json.loads(path.read_text());
    if d['status']!='SAT_LOCAL_WITNESS':continue
    S=set(d['selected']);window=[0]
    for k in d['directions']:window.append(window[-1]^(1<<k))
    centres=window[1:-1];B={v for v in range(512) if min((v^c).bit_count() for c in centres)<=4}
    assert S<=B and len(S)==len(d['selected']) and set(window)<=S
    adjacency={v:{v^(1<<k) for k in range(9)}&S for v in S}
    assert all(len(ns)<=2 for ns in adjacency.values())
    interior={v for v in S if all((v^(1<<k)) in B for k in range(9))}
    assert all(len(adjacency[v])>=1 for v in interior)
    ends={v for v in interior if len(adjacency[v])==1};assert len(ends)<=2
    # A finite degree-at-most-two induced graph is acyclic iff peeling degree0/1 removes all vertices.
    remaining=set(S)
    while remaining:
        peel={v for v in remaining if len(adjacency[v]&remaining)<=1}
        assert peel,'selected induced cycle';remaining-=peel
    alpha=[]
    for i,c in enumerate(centres,1):
        used={c^window[i-1],c^window[i+1]}
        alpha.append(sum((c^(1<<a)^(1<<b)) not in S for a,b in combinations(range(9),2) if (1<<a) not in used and (1<<b) not in used))
    assert alpha==d['census']['alpha'] and all(lo<=v<=hi for v,(lo,hi) in zip(alpha,d['bounds']))
    if 'outer_sum_cap' in d:assert sum(alpha[i] for i in [0,1,3,4])<=d['outer_sum_cap']
    rows.append(dict(probe=path.relative_to(HERE).as_posix(),sha256=sha(path),selected=len(S),alpha=alpha,interior_endpoints=len(ends)))
assert len(rows)==4
out=dict(status='PASS_FOUR_LOCAL_WITNESSES',witnesses=rows,script_sha256=sha(Path(__file__)),
    scope='Selected window, degree limits, interior positive degree and endpoint budget, acyclicity, exact counts and any sum cap checked independently. Boundary vertices retain the original relaxation; these are not complete snake witnesses.')
(HERE/'data/witness-audit.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
