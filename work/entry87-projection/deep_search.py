"""Continue selected highest-priority models with both parity clique bounds."""
from pathlib import Path
from itertools import combinations
import argparse,json,time
from fractions import Fraction
from exact_cover import components_partition
from saturation import separation
from solve import paths,model,save


def cliques(q,bits,profile):
    tr=components_partition(q,bits)
    out=[]
    for p,par in enumerate(profile):
        weighted={tuple(t["trace"]) for t in par["weights"] if Fraction(t["weight"])==1}
        clique=[i for i in range(p,len(tr),2) if tuple(sorted(tr[i])) in weighted]
        if clique:
            assert all(separation(tr[a],tr[b])<=1 for a,b in combinations(clique,2))
            out.append(clique)
    return out


if __name__=="__main__":
    ap=argparse.ArgumentParser()
    ap.add_argument("--bits",required=True)
    ap.add_argument("--budget",type=int)
    ap.add_argument("--out",type=Path,required=True)
    args=ap.parse_args()
    bits=[int(x) for x in args.bits]
    row=next(r for r in json.loads(Path("color-duals.json").read_text()) if r["bits"]==bits)
    q=paths()[1]
    families=cliques(q,bits,row["parities"])
    t=time.monotonic()
    print("start",bits,list(map(len,families)),flush=True)
    result=model(q,bits,args.budget,anchor_families=families)
    save(args.out,dict(bits=bits,budget=args.budget,cliques=families,
                       seconds=time.monotonic()-t,**result))
    print(result["status"],round(time.monotonic()-t),flush=True)
