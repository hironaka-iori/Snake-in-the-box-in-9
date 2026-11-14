"""Enumerate all feasible size profiles of four Q7 layers at total 193 vertices."""
import argparse,json,subprocess
from collections import Counter
from itertools import product
from pathlib import Path
from four_layer_bank import menus,test
from solve import save


def profiles():
    # Q7 has at most 51 vertices in an induced path. Four path components
    # contained in the layers have deficits 51-n_i with total 204-193=11.
    for d0 in range(12):
        for d1 in range(12-d0):
            for d2 in range(12-d0-d1):
                d3=11-d0-d1-d2
                sizes=tuple(51-d for d in (d0,d1,d2,d3))
                if sizes<=sizes[::-1]:yield sizes


if __name__=="__main__":
    p=argparse.ArgumentParser();p.add_argument("first",type=int);p.add_argument("stop",type=int)
    p.add_argument("--bank",type=Path,default=Path("highdim-seven-39.json"))
    p.add_argument("--nodes",type=int,default=180000000);a=p.parse_args()
    bank={k.encode():v for k,v in json.loads(a.bank.read_text())["forms"].items()}
    ms={n:menus(bank,n) for n in range(40,52)}
    orders=sorted(profiles(),key=lambda s:(-max(s[0],s[3]),-min(s),s))
    assert len(orders)==182
    path=Path(f"four-layer-lengths-{a.bank.stem}-{a.first}-{a.stop}-{a.nodes}.json");rows=[]
    for j in range(a.first,min(a.stop,len(orders))):
        ns=orders[j]
        # Begin at the end with fewer rooted shape choices to reduce search.
        if len(ms[ns[-1]])<len(ms[ns[0]]):ns=ns[::-1]
        if all(ms[n] for n in ns):r=test([ms[n] for n in ns],Path("four-layer-bank.exe").resolve(),a.nodes)
        else:r=dict(status="EMPTY",placements=0,nodes=0)
        rows.append(dict(index=j,sizes=ns,**r))
        save(path,rows)
        if r.get("vertices"):break
    print(len(rows),Counter(r["status"] for r in rows),sum(r["nodes"] for r in rows),flush=True)
