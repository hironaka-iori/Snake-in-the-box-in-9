"""Combine full and endpoint decisions, identifying the same forest across menus."""
import json
from collections import Counter, defaultdict
from pathlib import Path
from solve import defects, save


def snapshot():
    receipts=defaultdict(list)
    for path in sorted(Path(".").glob("three-cross-face-*-193-*.json")):
        r=json.loads(path.read_bytes())
        assert r["target"]==193
        if r.get("blocked_known"):
            continue
        if r["status"]=="FOUND":
            a=r["witness"];assert len(a)==193 and not defects(a)
        key=tuple(tuple(run) for run in r["forest"])
        receipts[key].append((path.name,r))
    result={}
    for group,menu in (("bank","three-cross-faces-menu.json"),("regrown","three-regrow--1-menu.json")):
        cases=[]
        for i,row in enumerate(json.loads(Path(menu).read_bytes())):
            key=tuple(tuple(run) for run in row["forest"])
            tips={v for run in key for v in (run[0],run[-1])}
            full=[];partial={};positive=[];open_runs=[]
            for name,r in receipts[key]:
                if r["status"]=="FOUND":
                    positive.append(name)
                elif r["status"]=="OPEN":
                    open_runs.append(name)
                elif "fixed_endpoint" in r:
                    assert r["fixed_endpoint"] in tips
                    partial[r["fixed_endpoint"]]=name
                else:
                    full.append(name)
            closed=bool(full) or set(partial)==tips
            assert not (closed and positive)
            cases.append(dict(index=i,status="FOUND" if positive else "UNSAT" if closed else "PENDING",
                              full=full,positive=positive,tips=partial,open_runs=open_runs))
        result[group]=dict(counts=dict(Counter(r["status"] for r in cases)),cases=cases)
    return result


if __name__=="__main__":
    census=snapshot()
    save(Path("three-face-census.json"),census)
    print({key:group["counts"] for key,group in census.items()})
