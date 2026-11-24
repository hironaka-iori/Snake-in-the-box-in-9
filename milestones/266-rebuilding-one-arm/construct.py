"""Place directed subpaths of long Q8 donors and regrow only the opposite arm."""
from argparse import ArgumentParser
from collections import Counter
from pathlib import Path
from tempfile import TemporaryDirectory
import subprocess
import sys

from catalogue import HERE, MS, PREV, checked, read, write
from growth import CSC, bank, digest


def run():
    cli=ArgumentParser()
    cli.add_argument("--steps",type=int,default=3500)
    args=cli.parse_args()
    files=[MS/"253-repeated-segment-growth/closure.json",MS/"255-parity-exchange-arms/focus-closure.json",
           MS/"259-four-exchange-component/new-arms.json",MS/"246-eight-dimensional-parents/donors.json"]
    raw=[]
    for f,field in zip(files,["paths","paths","shapes","shapes"]):
        rows=read(f)[field]
        raw.extend(rows.values() if isinstance(rows,dict) else [r["path"] for r in rows if len(r["path"])>=94])
    shapes={}
    for a in raw:
        def word(order):
            step=[x^y for x,y in zip(order,order[1:])]
            first=list(dict.fromkeys(step))
            return bytes(first.index(v) for v in step)
        shapes.setdefault(min(word(a),word(a[::-1])),a)
    donors=list(shapes.values())
    words,origins=bank.donor_suffixes(donors)
    images=list(bank.permutation_images())
    inputs=read(HERE/"parents.json")["parents"]
    out=HERE/"constructed.json"
    data=read(out) if out.exists() else dict(donors=len(donors),words=len(words),inputs={f.name+str(i):digest(f) for i,f in enumerate(files)},roots={})
    with TemporaryDirectory() as folder:
        exe=Path(folder)/"Grow.exe"
        subprocess.run([str(CSC),"/nologo","/optimize+","/out:"+str(exe),str(PREV/"JoinedSearch.cs")],capture_output=True,check=True)
        for i,(key,row) in enumerate(inputs.items()):
            if not row["from_191"] or key in data["roots"]:
                continue
            a=row["parent"]
            maps=bank.allowed_maps(a,images)
            best=bank.longest(words,maps)
            placed=bank.make_witness(donors,origins[best[1]],best,a)
            b=max([placed["partner"],*row["partners"].values()],key=len)
            rawout=subprocess.run([str(exe),str(26601+i),str(args.steps),"fixed"],text=True,
                input="".join(",".join(map(str,p))+"\n" for p in (a,b)),capture_output=True,check=True).stdout.splitlines()
            unchanged,candidate=(list(map(int,line.split(","))) for line in rawout[:2])
            assert unchanged==a
            w=checked(a,candidate)
            assert w["edges"]>=len(a)+len(b)-1
            data["roots"][key]=dict(placement=placed,steps=args.steps,seed=26601+i,best=w)
            write(out,data)
            print(key[:9],placed["joined_edges"],w["edges"],flush=True)
            if w["edges"]>=192:
                return

if __name__=="__main__":
    run()
