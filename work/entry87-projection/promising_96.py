"""Unrestricted completions of new 96-vertex middles admitting a long outer placement."""
import argparse,json
from pathlib import Path
from bank_pivots import canonical_word
from bank_two_arms import examine
from two_eight_layers import decode
from solve import BANK,save,defects

def ranked(remaining=False):
    results=json.loads(Path("middle-long-arm-96-0-1299-64-1-menu84.json").read_bytes())
    words=sorted(json.loads(Path("eight-regrow-96-32-160000000.json").read_bytes())["forms"])
    known={canonical_word(r["parent"]) for r in json.loads(Path("double-cross-bank.json").read_bytes())}
    choices=[]
    for row in results["rows"]:
        i=results["indices"][row["index"]];q=decode(words[i].encode())
        if bool(row["placements"])!=remaining and canonical_word(q) not in known:
            choices.append(dict(index=i,placements=row["placements"],parent=q))
    return sorted(choices,key=lambda r:(-r["placements"],r["index"]))

if __name__=="__main__":
    p=argparse.ArgumentParser();p.add_argument("start",type=int);p.add_argument("stop",type=int)
    p.add_argument("--target",type=int,choices=(192,193),default=193);p.add_argument("--budget",type=int,default=1200000)
    p.add_argument("--remaining",action="store_true")
    p.add_argument("--resume",action="store_true");a=p.parse_args()
    todo=ranked(a.remaining);assert len(todo)==(1251 if a.remaining else 47)
    if a.start==0:save(Path("remaining-96-menu.json" if a.remaining else "strong-96-menu.json"),todo)
    for row in todo[a.start:a.stop]:
        tag=f"long96-{row['index']}-{a.target}-{a.budget}"
        if a.resume:
            old=[json.loads(f.read_bytes()) for f in Path(".").glob(f"bank-two-long96-{row['index']}-*.json")]
            if any(r["status"]=="UNSAT" and r["outside_count"]+len(row["parent"])<=a.target for r in old):
                continue
            if any(r["tag"]==tag for r in old):continue
        result=examine(row,tag,a.budget,None,a.target)
        if result["witness"]:
            q=result["witness"];assert len(q)==a.target and not defects(q)
            if a.target==192:assert canonical_word(q) not in {canonical_word(r["vertex_sequence"]) for r in json.loads(BANK.read_bytes())}
            break
