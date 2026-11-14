"""Recover each two-face placement in the 191-edge bank, with a single shared root."""
from collections import Counter
import json
from solve import BANK,BANK_HASH,sha256,defects


def extract():
    raw=BANK.read_bytes();assert sha256(raw).hexdigest()==BANK_HASH
    out={}
    for i,r in enumerate(json.loads(raw)):
        q=r["vertex_sequence"]
        actions=[(a^b).bit_length()-1 for a,b in zip(q,q[1:])]
        for coord,count in Counter(actions).items():
            if count!=1:continue
            t=actions.index(coord)
            halves=[actions[:t][::-1],actions[t+1:]]
            halves.sort(key=len,reverse=True)
            assert list(map(len,halves))==[96,94]
            names={}
            canonical=tuple(tuple(names.setdefault(b,len(names)) for b in h) for h in halves)
            assert len(names)==8
            if canonical not in out:
                blocks=[]
                for h in canonical:
                    s=[0]
                    for b in h:s.append(s[-1]^(1<<b))
                    blocks.append(s)
                whole=blocks[0][::-1]+[x|256 for x in blocks[1]]
                assert len(whole)==192 and not defects(whole)
                out[canonical]=dict(parent=blocks[0],known_partner=blocks[1],sources=[])
            out[canonical]["sources"].append(dict(entry=i,hinge=coord))
    return list(out.values())


if __name__=="__main__":
    import argparse
    from pathlib import Path
    from joint_faces import solve
    parser=argparse.ArgumentParser()
    parser.add_argument("index",type=int);parser.add_argument("freedom",type=int)
    parser.add_argument("--budget",type=int,default=300000)
    parser.add_argument("--short-first",action="store_true");parser.add_argument("--positive",action="store_true")
    parser.add_argument("--checker",type=Path)
    parser.add_argument("--first-size",type=int,choices=range(94,100))
    a=parser.parse_args();rows=extract()
    solve(a.index,a.freedom,a.budget,a.short_first,"totalizer",rows[a.index],
          "pair"+str(a.index),a.positive,a.checker.resolve() if a.checker else None,a.first_size)
