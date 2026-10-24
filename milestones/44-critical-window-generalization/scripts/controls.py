"""Independent local-geometry and bank checks; no solver calls."""
from pathlib import Path
import hashlib,itertools,json
ROOT=Path(__file__).resolve().parents[3];HERE=Path(__file__).resolve().parents[1]
pairs=list(itertools.combinations(range(9),2))
def neighbors(v):return [v^(1<<d) for d in range(9)]
def count(S,v):return sum(not({v^(1<<a),v^(1<<b),v^(1<<a)^(1<<b)}&S) for a,b in pairs)
def canon(ds):
    labels={};return [labels.setdefault(d,len(labels)) for d in ds]
def components(S):
    todo=set(S);parts=[]
    while todo:
        seed=todo.pop();part={seed};queue=[seed]
        while queue:
            x=queue.pop()
            for y in neighbors(x):
                if y in todo:todo.remove(y);part.add(y);queue.append(y)
        parts.append(part)
    return parts
checked=[]
for file in sorted((HERE/'data').glob('*.json')):
    r=json.loads(file.read_text())
    if not isinstance(r,dict) or r.get('status')!='SAT':continue
    ds=r['directions'];W=[0]
    for d in ds:W.append(W[-1]^(1<<d))
    S=set(r['vertex_sequence'] if r.get('vertex_sequence') else r['selected'])
    full=r.get('vertex_sequence') is not None
    B=set(range(512)) if full else {v for v in range(512) if any((v^x).bit_count()<=4 for x in W[1:-1])}
    assert set(W)<=S<=B
    degree={v:len(S&set(neighbors(v))) for v in S}
    assert all(d<=2 for d in degree.values())
    interior={v for v in S if set(neighbors(v))<=B}
    assert all(degree[v]>=1 for v in interior)
    assert sum(degree[v]==1 for v in interior)<=2
    parts=components(S)
    assert all(sum(degree[v] for v in part)==2*(len(part)-1) for part in parts)
    counts=[count(S,v) for v in W[1:-1]]
    assert counts==r['census']['alpha']
    if 'caps' in r:assert all(a<=b for a,b in zip(counts,r['caps']))
    if r.get('joint'):
        pos,cap=r['joint'];assert sum(counts[j-1] for j in pos)<=cap
    if full:
        vs=r['vertex_sequence'];assert len(vs)==len(S) and len(parts)==1
        assert all(((vs[i]^vs[j]).bit_count()==1)==(j==i+1) for i in range(len(vs)) for j in range(i+1,len(vs)))
        assert vs[r['window_start']:r['window_start']+len(W)]==W
        assert sum(counts[j-1] for j in r['positions'])==r['cap']
    checked.append(dict(file=file.name,selected=len(S),components=len(parts),counts=counts,full_snake=full,sha256=hashlib.sha256(file.read_bytes()).hexdigest()))
bankfile=ROOT/'work/bank9.json';bank=json.loads(bankfile.read_text());hits=[]
for index,r in enumerate(bank):
    vs=r['vertex_sequence'];S=set(vs)
    assert len(S)==len(vs)==192
    assert all(((vs[i]^vs[j]).bit_count()==1)==(j==i+1) for i in range(len(vs)) for j in range(i+1,len(vs)))
    for reverse in [False,True]:
        ordered=vs[::-1] if reverse else vs
        ds=[(a^b).bit_length()-1 for a,b in zip(ordered,ordered[1:])]
        for start in range(len(ds)-7):
            if canon(ds[start:start+8])==[0,1,2,3,4,0,3,1]:
                counts=[count(S,ordered[start+j]) for j in [2,6]]
                assert sum(counts)>=7
                hits.append(dict(bank=index,reversed=reverse,start=start,counts=counts))
out=dict(status='PASS',local_and_full_checks=checked,bank_paths_checked=len(bank),bank_sha256=hashlib.sha256(bankfile.read_bytes()).hexdigest(),bank_occurrences=hits,minimum_bank_sum=min((sum(h['counts']) for h in hits),default=None),scope='Independent geometric and finite-bank controls; universal inequality is supplied separately by Lean.')
(HERE/'data/geometry-controls.json').write_text(json.dumps(out,indent=2)+'\n')
print('Checked',len(checked),'local/full witnesses,',len(bank),'bank snakes,',len(hits),'oriented occurrences; minimum bank sum',out['minimum_bank_sum'])
