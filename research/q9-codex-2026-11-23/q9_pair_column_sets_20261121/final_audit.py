import hashlib,itertools,json
from pathlib import Path
from collections import Counter
D=Path(__file__).resolve().parent
def load(fn):
    data=[json.loads(l) for l in (D/(fn+'.jsonl')).read_text().splitlines()]
    out={r['id']:r for r in data};assert len(out)==len(data);return out
def status(v):return dict(Counter(x['status'] for x in v.values()))
def complete(first,prefix,tail):
    a,b,c=[load(f) for f in (first,prefix,tail)];assert len(a)==288 and not(set(b)&set(c))
    assert set(b)|set(c)=={i for i in a if a[i]['status']=='UNKNOWN'}
    for r in (b,c):
        for i,x in r.items():assert (x['source'],x['axes'])==(a[i]['source'],a[i]['axes'])
    return a|b|c,dict(initial=status(a),retry=status(b|c))
a,sa=complete('allpairs_atleast','native_oct_prefix','native_oct_tail')
b,sb=complete('independent_wide','cadical_oct_prefix','cadical_oct_tail')
for i in a:assert a[i]['source']==b[i]['source'] and a[i]['axes']==b[i]['axes']
joint=Counter((a[i]['status'],b[i]['status']) for i in a)
for k in {r['source'] for r in a.values()}:
    assert {tuple(v['axes']) for v in a.values() if v['source']==k}==set(itertools.combinations(range(9),2))
single=load('single_oct');assert len(single)==72 and all(v['fixed']==0 and v['pool']==512 for v in single.values())
q=json.loads((D/'independent_oct_control.json').read_text())['witness']
assert len(q)==len(set(q))==192 and all(((x^q[j]).bit_count()==1)==(j==i+1) for i,x in enumerate(q) for j in range(i+1,len(q)))
blob=(D.parent/'q9_port_followup_public191.txt.gz').read_bytes()
print(json.dumps(dict(frozen_gzip_sha256=hashlib.sha256(blob).hexdigest(),axis_pairs=len(a),sources=sorted({r['source'] for r in a.values()}),target='at least 193 vertices',required_new_columns=False,native=sa,independent_cnfcadical=sb,joint={'+'.join(k):v for k,v in joint.items()},single_open_exact=status(load('single_open')),single_open_atleast=status(single),initial_independent_without_cell_bound=status(load('independent')),independent_positive_vertices=len(q),octagon_check=json.loads((D/'oct_verified.json').read_text()),small_atleast=json.loads((D/'small_atleast.json').read_text())),indent=2))
