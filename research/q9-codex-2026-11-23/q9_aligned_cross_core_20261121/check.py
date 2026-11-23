from collections import Counter,defaultdict
from itertools import combinations
from pathlib import Path
import json,subprocess,sys,random
D=Path(__file__).resolve().parent; ROOT=D.parent
sys.path[:0]=[str(ROOT/'q9_internal_xor_20261121'),str(ROOT)]
from verify import vertices,quadratic
from search_q9_anchored_sets import search
CUBE=set(range(512))
def parse(s):
    n,k,m,*v=map(int,s.split());assert len(v)==k+m
    return n,set(v[:k]),set(v[k:])
def line(n,c,x):
    return ' '.join(map(str,[n,len(c),len(x),*sorted(c),*sorted(x)]))
def result(p):
    assert len(p)==len(set(p)) and not quadratic(p)
    assert all((v^w).bit_count()==1 for v,w in zip(p,p[1:]))
def control():
    w=(ROOT/'q9_internal_xor_20261121/true190_all.words').read_text().splitlines()[0]
    p=vertices(w);result(p);rng=random.Random(128)
    output=[]
    for side in (0,1):
        half=set(p[side::2]); k=len(half); assert k in (95,96)
        missing=set(rng.sample(sorted(half),5))
        others=[v for v in range(512) if (v^p[side]).bit_count()%2==0 and v not in half]
        alternatives=set(rng.sample(others,5));core=half-missing;free=missing|alternatives
        txt=subprocess.check_output(['/tmp/q9_cross_core21','100000','0','190','1155'],input=line(k,core,free)+'\n',text=True)
        paths=[list(map(int,s.split()[1:])) for s in txt.splitlines() if s.startswith('FOUND ')]
        q,=paths;result(q);assert len(q)==191
        picked={v for v in q if (v^p[side]).bit_count()%2==0}
        assert core<=picked<=core|free and len(picked)==k
        output.append(dict(fixed_half=k,control_edges=len(q)-1,returned=q))
    return output

cases=[parse(l) for l in (D/'cases.dat').read_text().splitlines()]
meta=[json.loads(l) for l in (D/'cases.jsonl').read_text().splitlines()]
for (n,c,u),m in zip(cases,meta,strict=True):
    a=vertices(m['query']);b=vertices(m['donor']);perm=m['permutation']
    assert sorted(perm)==list(range(9))
    tr=lambda v: m['translation']^sum(1<<j for i,j in enumerate(perm) if v>>i&1)
    b=[tr(v) for v in b];i=m['query_offset'];j=m['donor_offset']
    assert a[i:i+33]==b[j:j+33]
    sa=set(a[m['side']::2]);sb=set(b[m['side']::2])
    assert len(sa)==len(sb)==n and c==sa&sb and u==sa^sb and 2*m['exchange_distance']==len(u)
reference=defaultdict(list)
counts=Counter()
for idx,(n,c,u) in enumerate(cases):
    if len(u)!=10 or len(reference[n])==4:continue
    reference[n].append(idx)
    opp={v for v in CUBE if (v^next(iter(c))).bit_count()%2}
    for mix in combinations(sorted(u),5):
        fixed=c|set(mix)
        st,w=search(fixed,fixed,192,12000,allowed=fixed|opp)
        counts[n,st]+=1
        if w: result(w);print(json.dumps(dict(idx=idx,witness=w)),flush=True)
print(json.dumps(dict(control=control(),checked_regions=len(cases),independent_region_ids=dict(reference),native_sat_counts={str(k):v for k,v in counts.items()})))
