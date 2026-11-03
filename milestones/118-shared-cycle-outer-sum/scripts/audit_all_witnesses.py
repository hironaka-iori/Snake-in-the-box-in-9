"""Independently verify every saved positive local-model witness."""
from pathlib import Path
from itertools import combinations
import hashlib,json
HERE=Path(__file__).resolve().parents[1]
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
rows=[]
for path in sorted((HERE/'data/probes').glob('*.json')):
    d=json.loads(path.read_text(encoding='utf-8'))
    if d['status']!='SAT_LOCAL_WITNESS':continue
    S=set(d['selected']);window=[0]
    for k in d['directions']:window.append(window[-1]^(1<<k))
    centres=window[1:-1]
    B={v for v in range(512) if min((v^c).bit_count() for c in centres)<=4}
    assert S<=B and len(S)==len(d['selected']) and set(window)<=S
    adjacency={v:{v^(1<<k) for k in range(9)}&S for v in S}
    assert all(len(ns)<=2 for ns in adjacency.values())
    interior={v for v in S if all((v^(1<<k)) in B for k in range(9))}
    assert all(len(adjacency[v])>=1 for v in interior)
    ends={v for v in interior if len(adjacency[v])==1}
    assert len(ends)<=2
    unseen=set(S);components=[]
    while unseen:
        component={unseen.pop()};todo=list(component)
        while todo:
            v=todo.pop()
            fresh=adjacency[v]&unseen
            unseen-=fresh;component|=fresh;todo.extend(fresh)
        edges=sum(len(adjacency[v]) for v in component)//2
        assert edges==len(component)-1
        components.append(len(component))
    alpha=[]
    for i,c in enumerate(centres,1):
        used={c^window[i-1],c^window[i+1]}
        alpha.append(sum((c^(1<<a)^(1<<b)) not in S for a,b in combinations(range(9),2)
            if (1<<a) not in used and (1<<b) not in used))
    assert alpha==d['census']['alpha'] and all(lo<=v<=hi for v,(lo,hi) in zip(alpha,d['bounds']))
    total=sum(alpha[i] for i in d['positions'])
    assert total<=d['cap']
    rows.append(dict(probe=path.relative_to(HERE).as_posix(),sha256=sha(path),selected=len(S),alpha=alpha,
        sum_positions=d['positions'],sum=total,cap=d['cap'],components=sorted(components,reverse=True),interior_endpoints=len(ends)))
assert len(rows)>=1
out=dict(status='PASS_SAVED_LOCAL_WITNESSES',witnesses=rows,script_sha256=sha(Path(__file__)),
    scope='Independently checked window inclusion, radius, degree, interior endpoint budget, component acyclicity, exact counts and sum. Boundary conditions remain relaxed; these are not complete snake constructions.')
path=HERE/'data/all-witness-audit.json';assert not path.exists()
path.write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
print('PASS_LOCAL_WITNESSES',len(rows))
for r in rows:print(r['probe'],r['alpha'],'components',len(r['components']))
