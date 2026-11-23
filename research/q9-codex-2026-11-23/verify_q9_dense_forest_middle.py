"""Rebuild all two-crossing port cases from the forest coordinates and replay the integer bounds."""
import gzip
import json
from itertools import product
from pathlib import Path
from verify_q8_forest_bank import decode
from verify_q9_intact98_all_crossings import integer_bound

def audit(src,certs):
    expected=set()
    for line in Path(src).read_text().splitlines():
        a,b=decode(line)
        low=frozenset(a+b)
        assert 0 in low
        for i,j in product((0,-1), repeat=2):
            ports=frozenset([a[i],b[j]])
            even=sum(v.bit_count()%2==0 for v in (a[-1-i],b[-1-j]))
            expected.add((low,ports,even))
    seen=set()
    edges=[]
    for line in gzip.open(certs,'rt'):
        r=json.loads(line)
        low=frozenset([0,*r['added']]);ports=frozenset(r['ports'])
        even=r['full'][0]; key=(low,ports,even)
        assert key in expected and key not in seen
        assert r['ends']==[0,0] and r['full']==[even,2-even]
        delta=sum((-1)**v.bit_count() for v in low) - (even-1)
        assert delta==r['delta']
        num=integer_bound(r['cert'],low,ports,[0,0],delta)
        assert num==r['numerator']
        bound=len(low)-1+num//r['cert']['scale']
        bound-=(bound%2)!=(even==1)
        assert bound==r['bound'] and bound<192
        seen.add(key);edges.append(bound)
    assert seen==expected
    return dict(port_cases=len(edges),max_upper_bound=max(edges),min_upper_bound=min(edges))

if __name__=='__main__':
    for bank,cert in [('q8_dense_forest_bank_round2.pts','q9_dense_forest_free_middle.jsonl.gz'),
                      ('q8_fresh_99_forests.pts','q9_fresh99_free_middle.jsonl.gz')]:
        print(json.dumps([bank,audit(bank,cert)]),flush=True)

