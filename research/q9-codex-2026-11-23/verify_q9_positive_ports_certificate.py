"""Verify one partition certificate by exhaustive subset enumeration in each Q4."""
import json
import sys
from itertools import combinations, permutations, product
from math import factorial
from pathlib import Path

def check():
    p=Path(sys.argv[1]) if len(sys.argv)>1 else Path(__file__).with_name("q9_positive_ports_220_certificate.json")
    record=json.loads(p.read_text())
    required=set()
    for a,b in record["required_edges"]:
        assert 0<=a<512 and 0<=b<512 and (a^b).bit_count()==1
        required.update((a,b))
    # Every stabilizing axis permutation preserves both statistics, even after translation.
    E={tuple(sorted(edge)) for edge in record["required_edges"]}
    groups={}
    for d in range(9):
        ones=sum((v>>d)&1 for v in required)
        signature=(min(ones,len(required)-ones),sum((a^b)==1<<d for a,b in E))
        groups.setdefault(signature,[]).append(d)
    stabilizer=0
    for choices in product(*(permutations(g) for g in groups.values())):
        perm={a:b for group,out in zip(groups.values(),choices) for a,b in zip(group,out)}
        def move(v):
            return sum(((v>>d)&1)<<perm[d] for d in range(9))
        permuted=[(move(a),move(b)) for a,b in E]
        anchor=permuted[0][0]
        for target in required:
            t=target^anchor
            stabilizer+=({tuple(sorted((a^t,b^t))) for a,b in permuted}==E)
    print("edge set stabilizer",stabilizer,"distinct symmetric edge sets",512*factorial(9)//stabilizer)
    def neighbors(v):
        return {v^(1<<i) for i in range(9)}
    mandatory_neighbors={v:neighbors(v)&required for v in range(512)}
    assert all(len(mandatory_neighbors[v])<=2 for v in required)
    saturated={v for v in required if len(mandatory_neighbors[v])==2}
    seen=set()
    capacities=[]
    for base,free in record["faces"]:
        assert 0<=base<512 and 0<=free<512 and free.bit_count()==4 and not base&free
        face={v for v in range(512) if v&~free==base}
        assert len(face)==16 and seen.isdisjoint(face)
        seen.update(face)
        must=face&required
        optional=sorted(v for v in face-must if not mandatory_neighbors[v]&saturated and len(mandatory_neighbors[v])<=2)
        def admissible(sel):
            adjacency={v:neighbors(v)&sel for v in sel}
            if any(len(adjacency[v]|mandatory_neighbors[v])>2 for v in sel):
                return False
            remaining=set(sel)
            while remaining:
                stack=[next(iter(remaining))]
                part=set(stack)
                while stack:
                    new=adjacency[stack.pop()]-part
                    stack.extend(new)
                    part.update(new)
                if all(len(adjacency[v])==2 for v in part):
                    return False
                remaining-=part
            return True
        cap=next(n+len(must) for n in range(len(optional),-1,-1)
                 if any(admissible(must|set(xs)) for xs in combinations(optional,n)))
        capacities.append(cap)
    assert seen==set(range(512))
    assert sum(capacities)-1==record["upper_edges"]
    print("required edges",len(record["required_edges"]),"required vertices",len(required),
          "faces",len(capacities),"sum of capacities",sum(capacities),"upper edges",sum(capacities)-1)
    print("face capacities",capacities)

if __name__=="__main__":
    check()
