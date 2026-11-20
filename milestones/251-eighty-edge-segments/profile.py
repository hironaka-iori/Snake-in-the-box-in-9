"""Bound each new rooted capacity and archive explicit long unrestricted partners."""
from argparse import ArgumentParser
from pathlib import Path
import subprocess
from tempfile import TemporaryDirectory

import partners251 as p

HERE = Path(__file__).resolve().parent


def main():
    cli = ArgumentParser(description=__doc__)
    cli.add_argument("--replay", action="store_true")
    args = cli.parse_args()
    census = HERE/"census-72.json"
    inherited = HERE/"replay-census-72-192.json"
    ledger = HERE/"profiles.json"
    pins = {**p.pins(census), "profile.py":p.file_hash(Path(__file__)),
            inherited.name:p.file_hash(inherited)}
    old, archived = p.known_parents()
    cases = p.census_cases(census,archived)
    proof = p.read(inherited)
    prior_rows = p.read(HERE/"partners-census-72.json")["records"]
    prior_caps = {(r["id"],r["end"]):r["length"]-1 for r in prior_rows
                  if r["target"]==191 and r["status"] in {"excluded","inherited"}}
    if (not proof["all_excluded"] or proof["ledger_sha256"]!=p.file_hash(HERE/"partners-census-72.json")
            or prior_caps.keys()!=cases.keys()):
        raise ValueError("Missing inherited unrestricted upper bound")
    index = p.placement_index(old)
    data = p.read(ledger) if ledger.exists() else dict(pins=pins,roots=[])
    if pins!=data["pins"]:
        raise ValueError("Source hashes differ")
    entries = {(r["id"],r["end"]):r for r in data["roots"]}
    if len(entries)!=len(data["roots"]) or not entries.keys()<=cases.keys():
        raise ValueError("Unexpected rooted record")
    with TemporaryDirectory(prefix="snake251-profiles-") as temporary:
        folder=Path(temporary)
        exe=folder/"VerifyLrat.exe"
        subprocess.run([str(p.joins.COMPILER),"/nologo","/optimize+","/out:"+str(exe),str(p.joins.CHECKER)],
                       capture_output=True,check=True,timeout=60)
        summary=[]
        for k,parent in cases.items():
            if k not in entries:
                if args.replay: raise ValueError("Missing root")
                q,_=p.joins.opposite.improve_seed(parent,[0],1.1,251+int(k[0][:6],16)+k[1])
                entries[k]=dict(id=k[0],end=k[1],initial=p.witness(parent,q),attempts=[])
            r=entries[k]
            low=r["initial"]["partner_edges"]; high=prior_caps[k]
            p.verified_partner(parent,r["initial"],low)
            best=r["initial"]
            attempts={a["length"]:a for a in r["attempts"]}
            if len(attempts)!=len(r["attempts"]): raise ValueError("Repeated query")
            candidates=p.transfers(parent,old,index)
            for n in list(attempts) if args.replay else [90,86,82,92,88,84,93,91]:
                if args.replay:
                    a=attempts[n]
                    p.replay(parent,n,a,old,folder,exe)
                else:
                    if n<=low or n>high: continue
                    if n not in attempts:
                        rules=p.active_cuts(candidates,n)
                        a=dict(length=n,**p.solve(parent,n,rules,old,folder,exe,2.5,None))
                        r["attempts"].append(a); attempts[n]=a
                    else:
                        a=attempts[n]
                if a["status"]=="witness" and n>low:
                    low=n; best=a
                if a["status"] in {"excluded","inherited"}: high=min(high,n-1)
                if low>high: raise ValueError("Bounds contradict")
            summary.append(dict(id=k[0],end=k[1],partner_lower=low,partner_upper=high,
                                joined_lower=low+len(parent),joined_upper=high+len(parent)))
            p.verified_partner(parent,best,low)
            if not args.replay:
                data["roots"]=list(entries.values())
                p.joins.save_json(ledger,data)
            print(k[0][:10],k[1],low,high,flush=True)
        if args.replay:
            p.joins.save_json(HERE/"profile-audit.json",dict(ledger_sha256=p.file_hash(ledger),bounds=summary))


if __name__=="__main__":
    main()
