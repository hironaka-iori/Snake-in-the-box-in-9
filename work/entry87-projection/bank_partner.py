"""Extend the five rooted 96-edge or five rooted 94-edge faces of known 191 snakes."""
import argparse
from collections import Counter
import json
from pathlib import Path
from partner_orbits import canonical
from partner93 import search
from solve import BANK,BANK_HASH,sha256,defects,save


def families():
    raw=BANK.read_bytes();assert sha256(raw).hexdigest()==BANK_HASH
    table={}
    for k,record in enumerate(json.loads(raw)):
        source=record["vertex_sequence"]
        moves=[(a^b).bit_length()-1 for a,b in zip(source,source[1:])]
        for axis,count in Counter(moves).items():
            if count!=1:continue
            cut=moves.index(axis)
            legs=(moves[:cut][::-1],moves[cut+1:])
            for first,other in (legs,legs[::-1]):
                key=(len(first),canonical(first))
                if key not in table:
                    names={}
                    blocks=[]
                    for seq in (first,other):
                        path=[0]
                        for axis2 in seq:
                            assert axis2!=axis
                            b=names.setdefault(axis2,len(names))
                            path.append(path[-1]^(1<<b))
                        blocks.append(path)
                    assert len(names)<=8 and set(blocks[0])&set(blocks[1])=={0}
                    check=blocks[0][::-1]+[v|256 for v in blocks[1]]
                    assert len(check)==192 and not defects(check)
                    table[key]=dict(parent=blocks[0],known_partner=blocks[1],sources=[])
                table[key]["sources"].append(dict(entry=k,hinge_axis=axis))
    groups={n:[v for (length,_),v in table.items() if length==n] for n in (94,96)}
    assert all(len(v)==5 for v in groups.values())
    return groups


if __name__=="__main__":
    parser=argparse.ArgumentParser()
    parser.add_argument("length",type=int,choices=(94,96))
    parser.add_argument("index",type=int,choices=range(5))
    parser.add_argument("--other-end",action="store_true")
    parser.add_argument("--budget",type=int,default=600000)
    parser.add_argument("--encoding",default="totalizer")
    parser.add_argument("--checker",type=Path)
    a=parser.parse_args()
    row=families()[a.length][a.index]
    p=row["parent"]
    root=p[-1] if a.other_end else 0
    tag=f"bank{a.length}-{a.index}-"+("far" if a.other_end else "join")
    r=search(root,a.budget,a.encoding,"cadical195",first_cuts=True,
             vertex_target=192-a.length,parent_path=p,label=tag,
             checker=a.checker.resolve() if a.checker else None)
    if r["status"]=="FOUND":
        assert len(r["vertices"])==193 and not defects(r["vertices"])
