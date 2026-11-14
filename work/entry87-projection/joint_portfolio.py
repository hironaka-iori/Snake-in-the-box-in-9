"""Cover every allowed length split around specified one-crossing bank placements."""
import argparse
from pathlib import Path
from joint_faces import solve
from paired_seeds import extract


if __name__=="__main__":
    parser=argparse.ArgumentParser()
    parser.add_argument("start",type=int);parser.add_argument("stop",type=int)
    parser.add_argument("freedom",type=int)
    parser.add_argument("--budget",type=int,default=400000)
    parser.add_argument("--sizes",type=int,nargs="+",default=list(range(94,100)))
    parser.add_argument("--checker",type=Path)
    args=parser.parse_args()
    source=extract()
    for i in range(args.start,args.stop):
        for n in args.sizes:
            tag=f"pair{i}"
            result=Path(f"joint-faces-{tag}-{args.freedom}-{n}-totalizer"+
                        ("-checked" if args.checker else "")+".json")
            if result.exists():
                import json
                row=json.loads(result.read_text())
                if row["status"] in ("FOUND","UNSAT"):continue
            solve(i,args.freedom,args.budget,False,"totalizer",source[i],tag,
                  False,args.checker.resolve() if args.checker else None,n)
