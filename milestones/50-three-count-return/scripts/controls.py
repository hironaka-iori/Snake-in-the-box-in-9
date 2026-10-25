"""Independently count saved local configurations and all bank occurrences."""
from pathlib import Path
import hashlib,itertools,json
ROOT=Path(__file__).resolve().parents[3];HERE=Path(__file__).resolve().parents[1]
pairs=list(itertools.combinations(range(9),2))
def nb(v):return {v^(1<<d) for d in range(9)}
def count(S,v):return sum(not({v^(1<<a),v^(1<<b),v^(1<<a)^(1<<b)}&S) for a,b in pairs)
def canon(ds):
    names={};return [names.setdefault(d,len(names)) for d in ds]
checked=[]
for file in sorted((HERE/'data').rglob('*.json')):
    r=json.loads(file.read_text())
    if not isinstance(r,dict) or r.get('status')!='SAT':continue
    if 'vertex_sequence' in r:continue  # Full-snake witnesses have separate all-pairs checks in verify.py.
    ds=r['directions'];W=[0]
    for d in ds:W.append(W[-1]^(1<<d))
    S=set(r['selected']);B={v for v in range(512) if any((v^x).bit_count()<=4 for x in W[1:-1])}
    assert set(W)<=S<=B
    degree={v:len(S&nb(v)) for v in S};assert all(d<=2 for d in degree.values())
    interior={v for v in S if nb(v)<=B}
    assert all(degree[v]>=1 for v in interior) and sum(degree[v]==1 for v in interior)<=2
    todo=set(S);components=0
    while todo:
        seed=todo.pop();part={seed};queue=[seed]
        while queue:
            x=queue.pop()
            for y in nb(x)&todo:todo.remove(y);part.add(y);queue.append(y)
        assert sum(degree[v] for v in part)==2*(len(part)-1);components+=1
    alpha=[count(S,v) for v in W[1:-1]]
    assert alpha==r['census']['alpha'] and all(a<=b for a,b in zip(alpha,r['caps']))
    if r.get('joint') is not None:
        positions,cap=r['joint'];assert sum(alpha[j-1] for j in positions)<=cap
    checked.append(dict(file=file.relative_to(HERE/'data').as_posix(),selected=len(S),components=components,counts=alpha,sha256=hashlib.sha256(file.read_bytes()).hexdigest()))
cases=json.loads((HERE/'data/cases.json').read_text());bankfile=ROOT/'work/bank9.json';bank=json.loads(bankfile.read_text());hits=[]
for index,r in enumerate(bank):
    vs=r['vertex_sequence'];S=set(vs);assert len(S)==len(vs)==192
    assert all(((vs[i]^vs[j]).bit_count()==1)==(j==i+1) for i in range(len(vs)) for j in range(i+1,len(vs)))
    for reverse in [False,True]:
        ordered=vs[::-1] if reverse else vs;ds=[(a^b).bit_length()-1 for a,b in zip(ordered,ordered[1:])]
        for case in cases:
            L=len(case['dirs'])
            for start in range(len(ds)-L+1):
                if canon(ds[start:start+L])!=case['dirs']:continue
                alpha=[count(S,ordered[start+j]) for j in case['positions']]
                if case['kind']=='sum':assert sum(alpha)>case['cap']
                else:assert not all(a<=b for a,b in zip(alpha,case['caps']))
                hits.append(dict(bank=index,reversed=reverse,case=case['number'],start=start,counts=alpha))
summary=[dict(case=r['number'],occurrences=sum(h['case']==r['number'] for h in hits),minimum_sum=min((sum(h['counts']) for h in hits if h['case']==r['number']),default=None)) for r in cases]
out=dict(status='PASS',local_checks=checked,bank_paths_checked=len(bank),bank_sha256=hashlib.sha256(bankfile.read_bytes()).hexdigest(),bank_occurrences=hits,summary=summary,scope='Finite controls; universal exclusions are supplied separately by Lean.')
(HERE/'data/geometry-controls.json').write_text(json.dumps(out,indent=2)+'\n')
print('Checked',len(checked),'local configurations and',len(bank),'complete bank paths;',summary)
