"""Use certified sibling bounds to force visits to sites freed by each remaining parent."""
from argparse import ArgumentParser
from pathlib import Path
import subprocess
from tempfile import TemporaryDirectory
from time import monotonic
import fixed
from family import read, file_hash, require, root_family, solver
from family_cuts import sources

HERE=Path(__file__).resolve().parent
LEDGER=HERE/"forced-caps.json"


def main():
    ap=ArgumentParser(description=__doc__)
    ap.add_argument("--seconds",type=int,default=18)
    ap.add_argument("--total",type=int,default=100)
    ap.add_argument("--lengths",type=int,nargs="+",default=[95])
    ap.add_argument("--replay",action="store_true")
    args=ap.parse_args()
    old,pins=sources()
    shapes=read(HERE/"parity-families.json")["shapes"]
    inputs=read(HERE/"individual-caps.json")["cases"]
    for tag,entries in inputs.items():
        k,s=tag.split(":");root=int(s)
        p=root_family(shapes,root)[0][k]
        direct=[int(t)-1 for t,r in entries.items() if r["status"] in ("excluded","inherited")]
        if direct:old["individual/"+tag,0]=(p,min(direct))
    for f in (Path(__file__),HERE/"individual-caps.json",HERE/"individual-replay.json"):
        pins[f.name]=file_hash(f)
    require(read(HERE/"individual-replay.json")["ledger"]==pins["individual-caps.json"],"Unreplayed prior proof")
    ix=solver.placement_index(old)
    results=read(LEDGER) if LEDGER.exists() else dict(pins=pins,attempts={})
    require(results["pins"]==pins,"Premises changed")
    until=monotonic()+args.total
    with TemporaryDirectory(prefix="snake254-forced-") as temp:
        folder=Path(temp);checker=folder/"VerifyLrat.exe";trimmer=folder/"TrimLrat.exe"
        for src,exe in ((solver.joins.CHECKER,checker),(fixed.R252/"TrimLrat.cs",trimmer)):
            subprocess.run([str(solver.joins.COMPILER),"/nologo","/optimize+","/out:"+str(exe),str(src)],check=True)
        for root in (161,1):
            paths,_,_=root_family(shapes,root)
            for k,p in sorted(paths.items()):
                tag=k+":"+str(root)
                cases=results["attempts"].setdefault(tag,{})
                if not args.replay and any(set(v)==set(p) and hi<95 for v,hi in old.values()):continue
                candidates=solver.transfers(p,old,ix)
                for n in (sorted(map(int,cases)) if args.replay else args.lengths):
                    previous=cases.get(str(n))
                    if args.replay:
                        solver.replay(p,n,previous,old,folder,checker)
                    else:
                        if monotonic()>=until:break
                        if any(int(m)<=n and v["status"] in ("excluded","inherited") for m,v in cases.items()):continue
                        rules=solver.active_cuts(candidates,n)
                        rec=solver.solve(p,n,rules,old,folder,checker,min(args.seconds,max(.01,until-monotonic())),previous)
                        fixed.compact(folder,checker,trimmer,rec)
                        cases[str(n)]=rec;solver.joins.save_json(LEDGER,results)
                        print(root,k[:8],n,[r["sites"] for r in rules],rec["status"],flush=True)
        if args.replay:solver.joins.save_json(HERE/"forced-replay.json",dict(ledger=file_hash(LEDGER),
                                                  checked=sum(len(v) for v in results["attempts"].values())))


if __name__=="__main__":main()
