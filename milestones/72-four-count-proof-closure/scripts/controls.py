"""Check local witnesses and all bank occurrences by direct cube adjacency."""
from pathlib import Path
import hashlib,itertools,json
HERE=Path(__file__).resolve().parents[1];ROOT=HERE.parents[1]
pairs=list(itertools.combinations(range(9),2));nb=lambda v:{v^(1<<d) for d in range(9)}
def alpha(S,v):return sum(not({v^(1<<a),v^(1<<b),v^(1<<a)^(1<<b)}&S) for a,b in pairs)
def canon(w):
    n={};return [n.setdefault(d,len(n)) for d in w]
controls=[]
for p in (HERE/'data').glob('*.json'):
    r=json.loads(p.read_text())
    if not isinstance(r,dict) or r.get('status')!='SAT' or not r.get('selected'):continue
    ds=r.get('dirs',r.get('directions'));W=[0]
    for d in ds:W.append(W[-1]^(1<<d))
    S=set(r['selected']);B={v for v in range(512) if any((v^x).bit_count()<=4 for x in W[1:-1])}
    assert set(W)<=S<=B
    degrees={v:len(S&nb(v)) for v in S};assert max(degrees.values())<=2
    interior={v for v in S if nb(v)<=B}
    assert all(degrees[v]>=1 for v in interior) and sum(degrees[v]==1 for v in interior)<=2
    remaining=set(S);components=0
    while remaining:
        root=remaining.pop();part={root};queue=[root]
        while queue:
            for v in nb(queue.pop())&remaining:remaining.remove(v);part.add(v);queue.append(v)
        assert sum(degrees[v] for v in part)==2*(len(part)-1);components+=1
    counts=[alpha(S,v) for v in W[1:-1]]
    if 'bounds' in r:assert all(lo<=x<=hi for x,(lo,hi) in zip(counts,r['bounds']))
    if r.get('joint'):assert sum(counts[j-1] for j in r['joint'][0])<=r['joint'][1]
    controls.append(dict(file=p.name,sha256=hashlib.sha256(p.read_bytes()).hexdigest(),counts=counts,components=components,vertices=len(S)))
cases=json.loads((HERE/'data/cases.json').read_text());bankpath=ROOT/'work/bank9.json';bank=json.loads(bankpath.read_text());occurrences=[]
for k,row in enumerate(bank):
    vs=row['vertex_sequence'];S=set(vs);assert len(vs)==len(S)==192
    assert all(((a^b).bit_count()==1)==(j==i+1) for i,a in enumerate(vs) for j,b in enumerate(vs) if i<j)
    cache={v:alpha(S,v) for v in vs[1:-1]}
    for reverse in [False,True]:
        ordered=vs[::-1] if reverse else vs;ds=[(u^v).bit_length()-1 for u,v in zip(ordered,ordered[1:])]
        for r in range(len(ds)-4):
            w=canon(ds[r:r+5]);counts=[cache[ordered[r+j]] for j in range(1,5)]
            for c in cases:
                if w!=c['dirs']:continue
                assert not all(lo<=x<=hi for x,(lo,hi) in zip(counts,c['bounds']))
                occurrences.append(dict(bank=k,reversed=reverse,start=r,case=c['number'],counts=counts))
out=dict(status='PASS',local_controls=controls,bank_paths=len(bank),bank_sha256=hashlib.sha256(bankpath.read_bytes()).hexdigest(),occurrences=len(occurrences),per_case={c['number']:sum(r['case']==c['number'] for r in occurrences) for c in cases},scope='Finite controls. A local forest need not extend to a complete snake. Universal exclusions require Lean proofs.')
(HERE/'data/controls.json').write_text(json.dumps(out,indent=2)+'\n');print(out)
