"""Independently reconstruct completions with direct neighbour counts and edge selection."""
from collections import defaultdict
from itertools import combinations
from math import comb
from pathlib import Path
import json
import subprocess
import sys
from tempfile import TemporaryDirectory

HERE=Path(__file__).resolve().parent
from enumerate_shell import MS, read, digest, check_path
from replay_exchange import CSC


def replay(data, radius, exe):
    path=data["reference"]
    seed=set(path[1::2])
    raw=subprocess.run([str(exe),str(radius)],input=",".join(map(str,sorted(seed)))+"\n",
                       text=True,capture_output=True,check=True).stdout
    seen={}
    active=None
    recovered=defaultdict(list)
    subtotal=0
    reported=None
    for line in raw.splitlines():
        op,*args=line.split()
        if op=="C":
            i,remove,add=args
            if active is not None or int(i)!=len(seen):
                raise ValueError("Case order differs")
            active=(tuple(map(int,remove.split(","))),tuple(map(int,add.split(","))))
            if active in seen: raise ValueError("Case repeated")
            seen[active]=int(i)
        elif op=="P":
            p=tuple(map(int,args[2].split(",")))
            check_path(p)
            if (len(p)!=97 or active is None or int(args[0])!=seen[active] or
                set(p[1::2])!=(seed-set(active[0]))|set(active[1])):
                raise ValueError("Path and selected class differ")
            recovered[active].append(min(p,p[::-1]))
        elif op=="S":
            if int(args[0])!=seen[active] or int(args[-1])!=len(recovered.get(active,[])):
                raise ValueError("Path count mismatch")
            subtotal+=int(args[-1])
            active=None
        elif op=="T":
            reported=tuple(map(int,args))
        else: raise ValueError(op)
    expected={(tuple(r["removed"]),tuple(r["inserted"])):
              sorted(min(tuple(a["vertices"]),tuple(a["vertices"][::-1])) for a in r["paths"])
              for r in data["positive_classes"]}
    if (active is not None or reported!=(comb(48,radius),len(seen)) or
            {a:sorted(b) for a,b in recovered.items()}!=expected or
            subtotal!=data["counts"]["labelled"] or len(seen)!=data["counts"]["pass_supply"]):
        raise ValueError(("Enumerations disagree",reported,subtotal,data["counts"]))
    return dict(cases=comb(48,radius)*comb(80,radius),removed_sets=reported[0],
                supply_survivors=len(seen),positive_sides=len(expected),paths=subtotal)


def main():
    folder=Path(sys.argv[1]).resolve()
    radius=int(sys.argv[2])
    native=MS/"255-parity-exchange-arms/replay_exchange.cs"
    driver=HERE/"EnumerateExchanges.cs"
    ledger={}
    with TemporaryDirectory() as temp:
        exe=Path(temp)/"scan.exe"
        subprocess.run([str(CSC),"/nologo","/optimize+","/main:EnumerateExchanges","/out:"+str(exe),
                        str(native),str(driver)],capture_output=True,check=True)
        for source in sorted(folder.glob("shell-*.json")):
            ledger[source.name]={"sha256":digest(source),**replay(read(source),radius,exe)}
    out=dict(radius=radius,inputs={p.name:digest(p) for p in [Path(__file__),native,driver,CSC]},shells=ledger)
    (folder/"replay.json").write_text(json.dumps(out,indent=2)+"\n",encoding="utf-8",newline="\n")
    print({k:v["paths"] for k,v in ledger.items()})

if __name__=="__main__":
    main()
