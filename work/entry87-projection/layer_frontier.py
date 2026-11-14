"""Collect the remaining absolute A,C paths and merge identical rooted decisions up to coordinate naming."""
from itertools import permutations
import json
from pathlib import Path
from solve import defects,save


def canonical(a,c):
    origin=a[0];axes=[]
    for q in (a,c):
        for x,y in zip(q,q[1:]):
            j=(x^y).bit_length()-1
            if j not in axes:axes.append(j)
    best=None
    for rem in permutations(i for i in range(7) if i not in axes):
        order=axes+list(rem)
        def path(q):return tuple(sum((((v^origin)>>j)&1)<<t for t,j in enumerate(order)) for v in q)
        key=(path(a),path(c))
        if best is None or key<best:best=key
    return best


if __name__=="__main__":
    groups={};total=0;indices=set()
    for f in sorted(Path().glob("one-layer-core-*-15-10000-750000-index.json")):
        for row in json.loads(f.read_text()):
            assert row["index"] not in indices;indices.add(row["index"])
            assert len(row["open_cases"])+row["excluded_selected"]==row["selected"]
            a=row["first"]
            for r in row["open_cases"]:
                c=r["third"];assert not defects(a) and not defects(c)
                key=canonical(a,c);total+=1
                if key not in groups:
                    u=set(range(128))-set(key[0])-set(key[1])
                    groups[key]=dict(first=key[0],third=key[1],middle_domain=sorted(u|{key[0][-1],key[1][0]}),
                                     final_domain=sorted(u|{key[1][-1]}),required_sum=r["required_sum"],
                                     middle_lower=r["middle_lower"],middle_upper=r["middle_upper"],
                                     last_lower=r["last_lower"],last_upper=r["last_upper"],occurrences=[])
                g=groups[key];g["occurrences"].append(row["index"])
                for k in ("middle_lower","last_lower"):g[k]=max(g[k],r[k])
                for k in ("middle_upper","last_upper"):g[k]=min(g[k],r[k])
    assert len(indices)==30 and total==382
    rows=sorted(groups.values(),key=lambda g:(g["middle_upper"]+g["last_upper"]-g["required_sum"],
                                              g["required_sum"]-g["middle_lower"]-g["last_lower"]))
    save(Path("one-layer-frontier.json"),dict(indexed=total,distinct=len(rows),cases=rows))
    print(total,len(rows),sum(r["middle_upper"]+r["last_upper"]>=r["required_sum"] for r in rows))
