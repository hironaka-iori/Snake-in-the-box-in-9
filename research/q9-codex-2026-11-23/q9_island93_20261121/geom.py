from collections import defaultdict
from pathlib import Path
import gzip,json
D=Path(__file__).resolve().parent;R=D.parent;old=R/'q9_lower_island_edge_20261121'
cases=list(map(json.loads,(old/'cases.jsonl').read_text().splitlines()))
def geometry(i,code):
    c=cases[i];p=c['lo'];a,b=c['edge'];L=set(p)|{a,b}
    # Determine the specified ports by enumerating terminal subsets and testing colours and degrees.
    import itertools
    found=[]
    terminals=(p[0],p[-1],a,b)
    for P in itertools.combinations(terminals,2+(code&1)):
        P=set(P); tips=set(terminals)-P
        if P&{a,b}!={c['edge'][code//2]} or len({x.bit_count()%2 for x in tips})!=1:continue
        m=next(iter(tips)).bit_count()%2
        eps=[int(m==j)*(2-len(tips)) for j in (0,1)]
        delta=sum((-1)**x.bit_count() for x in L)-(-1)**m
        found.append((L,P,m,eps,delta))
    assert len(found)==1
    return found[0]
def regs():
    out={};recs=[]
    for f in sorted(D.glob('pass*.jsonl')):
        for line in f.read_text().splitlines():
            if not line.endswith('}'):continue
            r=json.loads(line);key=r['i'],r['c'];recs.append(r)
            if 'file' in r and (key not in out or r['score']<out[key]['score']):out[key]=r
    return out,recs
