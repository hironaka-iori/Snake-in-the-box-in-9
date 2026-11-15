"""Resume the four disjoint fixed-endpoint decisions on unresolved face forests."""
import argparse
import json
from pathlib import Path
from three_cross_faces import decide


if __name__ == "__main__":
    parser=argparse.ArgumentParser()
    parser.add_argument("--original", action="store_true")
    parser.add_argument("--start", type=int, default=0)
    parser.add_argument("--stop", type=int, default=41)
    parser.add_argument("--budget", type=int, default=1200000)
    args=parser.parse_args()
    source="three-cross-faces-menu.json" if args.original else "three-regrow--1-menu.json"
    rows=json.loads(Path(source).read_bytes())
    for i in range(args.start,min(args.stop,len(rows))):
        name=str(i) if args.original else f"r-1-{i}"
        prefix=f"three-cross-face-{name}-193-"
        solved=set()
        for path in Path(".").glob(prefix+"*.json"):
            if path.name.endswith("-new.json"):
                continue
            r=json.loads(path.read_bytes())
            assert r["forest"]==rows[i]["forest"] and r["target"]==193
            if r["status"]=="FOUND":
                print("witness",path,flush=True)
                raise SystemExit
            if r["status"]=="UNSAT":
                if "fixed_endpoint" in r:
                    solved.add(r["fixed_endpoint"])
                else:
                    solved.update(v for run in r["forest"] for v in (run[0],run[-1]))
        tips=sorted(v for run in rows[i]["forest"] for v in (run[0],run[-1]))
        for k,tip in enumerate(tips):
            if tip in solved:
                continue
            decide(rows[i],name,193,args.budget,endpoint=k)
            result=Path(f"{prefix}{args.budget}-tip{k}.json")
            if json.loads(result.read_bytes())["status"]=="FOUND":
                raise SystemExit
