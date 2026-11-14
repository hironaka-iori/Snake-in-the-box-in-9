"""Exact integer check of a rational point in the proposed round-218 relaxation."""
from pathlib import Path
import json
from partner93 import source_parent
from partner_cuts import abstract_cycles
from itertools import combinations


def verify(file):
    data=json.loads(file.read_text())
    den=data["denominator"];root=data["root"]
    x={int(w):v for w,v in data["selected_numerators"].items()}
    e={int(w):v for w,v in data["endpoint_numerators"].items()}
    allowed=(set(range(256))-set(source_parent()))|{root}
    assert set(x)==allowed and set(e)=={w for w in allowed if w.bit_count()%2}
    assert all(0<=v<=den for v in x.values()) and all(0<=v<=x[w] for w,v in e.items())
    assert sum(e.values())==den and x[root]==den
    assert sum(x[w] for w in e)*2==sum(x.values())==data["total_numerator"]
    for v in allowed:
        neighbours=[w for w in allowed if (v^w).bit_count()==1]
        selected=sum(x[w] for w in neighbours);d=len(neighbours)
        if v==root:assert selected==den
        else:assert 2*x[v]-e.get(v,0)<=selected<=d*den-(d-2)*x[v]-e.get(v,0)
    cycles=set()
    for order in (2,3):
        for dims in combinations(range(8),order):
            mask=sum(1<<j for j in dims)
            put=[sum(((v>>i)&1)<<j for i,j in enumerate(dims)) for v in range(1<<order)]
            for base in range(256):
                if base&mask:continue
                for c in abstract[order]:
                    points=frozenset(base|put[v] for v in c)
                    if points<=allowed:cycles.add(points)
    for c in cycles:assert sum(x[w] for w in c)<=den*(len(c)-1)
    assert len(cycles)==(279 if root==0 else 274)
    return root,sum(x.values()),den,len(cycles)


abstract={d:[c for c in abstract_cycles(d) if len(c)==2*d] for d in (2,3)}
if __name__=="__main__":
    import sys
    for filename in sys.argv[1:]:
        print(verify(Path(filename)))
