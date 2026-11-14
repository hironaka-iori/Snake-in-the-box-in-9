"""Use each new regrown 97-vertex middle with two unrestricted outer arms."""
import argparse,json
from pathlib import Path
from bank_pivots import canonical_word
from bank_two_arms import examine
from two_eight_layers import decode
from solve import save

def middle_menu():
    forms=json.loads(Path("eight-regrow-97-37-160000000.json").read_bytes())["forms"]
    known={}
    for i in range(5):
        f=Path(f"bank-two-96-{i}-checked.json")
        r=json.loads(f.read_bytes());assert r["status"]=="UNSAT"
        known[canonical_word(r["exact_parent"])]=f.name
    shapes={canonical_word(decode(word.encode())) for word in forms}
    assert len(shapes)==51 and set(known)<=shapes
    return [decode(bytes(48+b for b in word)) for word in sorted(shapes-set(known))]

if __name__=="__main__":
    p=argparse.ArgumentParser();p.add_argument("start",type=int);p.add_argument("stop",type=int)
    p.add_argument("--budget",type=int,default=200000);a=p.parse_args()
    paths=middle_menu();assert len(paths)==46
    if a.start==0:save(Path("regrown-middles-menu.json"),paths)
    for i in range(a.start,min(a.stop,len(paths))):
        r=examine(dict(parent=paths[i]),f"regrown97-{i}-{a.budget}",a.budget,None)
        if r["witness"]:break
