"""Extract the complete middle face of every bank path crossing a direction twice."""
import argparse,json
from collections import Counter
from pathlib import Path
from bank_two_arms import examine
from fixed_face import solve_face
from partner_orbits import canonical
from solve import BANK,BANK_HASH,sha256,defects,save


def cases():
    raw=BANK.read_bytes();assert sha256(raw).hexdigest()==BANK_HASH
    rows={}
    for i,r in enumerate(json.loads(raw)):
        path=r["vertex_sequence"];moves=[(a^b).bit_length()-1 for a,b in zip(path,path[1:])]
        for axis,multiplicity in Counter(moves).items():
            if multiplicity!=2:continue
            a,b=[j for j,m in enumerate(moves) if m==axis]
            middle=moves[a+1:b]
            key=min(canonical(middle),canonical(middle[::-1]))
            if key not in rows:
                vertices=[0]
                for move in key:vertices.append(vertices[-1]^(1<<move))
                assert max(vertices)<256 and not defects(vertices)
                rows[key]=dict(parent=vertices,edges=len(middle),occurrences=[])
            runs=[path[:a+1],path[a+1:b+1],path[b+1:]]
            assert all((v>>axis&1)==(runs[0][0]>>axis&1) for v in runs[0]+runs[2])
            assert all((v>>axis&1)!=(runs[0][0]>>axis&1) for v in runs[1])
            rows[key]["occurrences"].append(dict(entry=i,axis=axis,first=a,last=b,
                                                arms=[a,len(path)-2-b]))
    ordered=sorted(rows.values(),key=lambda r:-r["edges"])
    assert [(r["edges"],len(r["occurrences"])) for r in ordered]==[(95,84),(93,2),(92,2)]
    return ordered


if __name__=="__main__":
    p=argparse.ArgumentParser();p.add_argument("index",type=int,choices=range(3))
    p.add_argument("--budget",type=int,default=3500000);p.add_argument("--checker",type=Path)
    p.add_argument("--two",action="store_true")
    a=p.parse_args();rs=cases();s=rs[a.index]
    save(Path("double-cross-bank.json"),rs)
    tag=f"doublebank-{a.index}-{s['edges']}"
    checker=a.checker.resolve() if a.checker else None
    if a.two:examine(s,tag,a.budget,checker)
    else:solve_face(s["parent"],tag,a.budget,checker,4)
