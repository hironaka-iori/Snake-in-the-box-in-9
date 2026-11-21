"""Resolve individual parents left open by the simultaneous obstruction model."""
from argparse import ArgumentParser
from pathlib import Path
from tempfile import TemporaryDirectory
from time import monotonic
import subprocess
import fixed
import family_cuts
from family import solver, read, file_hash, require, root_family

HERE=Path(__file__).resolve().parent
LEDGER=HERE/"individual-caps.json"


def main():
    cli=ArgumentParser(description=__doc__)
    cli.add_argument("--roots",nargs="+",type=int,default=[161,1])
    cli.add_argument("--lengths",nargs="+",type=int,default=[95])
    cli.add_argument("--seconds",type=int,default=10)
    cli.add_argument("--total",type=int,default=125)
    cli.add_argument("--replay",action="store_true")
    args=cli.parse_args()
    old,pins=family_cuts.sources();index=solver.placement_index(old)
    pins["individual.py"]=file_hash(Path(__file__))
    d=read(LEDGER) if LEDGER.exists() else dict(pins=pins,cases={})
    require(d["pins"]==pins,"Inputs changed")
    shapes=read(HERE/"parity-families.json")["shapes"]
    with TemporaryDirectory(prefix="snake254-individual-") as name:
        folder=Path(name);checker=folder/"VerifyLrat.exe";trimmer=folder/"TrimLrat.exe"
        for src,exe in ((solver.joins.CHECKER,checker),(fixed.R252/"TrimLrat.cs",trimmer)):
            subprocess.run([str(solver.joins.COMPILER),"/nologo","/optimize+","/out:"+str(exe),str(src)],check=True)
        until=monotonic()+args.total
        for root in args.roots:
            paths,_,_=root_family(shapes,root)
            for k,p in sorted(paths.items()):
                tag=k+":"+str(root)
                rows=d["cases"].setdefault(tag,{})
                candidates=solver.transfers(p,old,index)
                for length in (sorted(map(int,rows)) if args.replay else args.lengths):
                    rules=solver.active_cuts(candidates,length);prev=rows.get(str(length))
                    if args.replay:
                        require(prev["status"]=="inherited" or prev["rules"]==rules,"Regenerated cuts differ")
                        solver.replay(p,length,prev,old,folder,checker)
                    else:
                        if any(v["status"] in ("excluded","inherited") and int(m)<=length for m,v in rows.items()):continue
                        if any(v["status"]=="witness" and int(m)>=length for m,v in rows.items()):continue
                        if any(set(p)==set(q) and c<length for q,c in old.values()):
                            rec=next(r for r in candidates if len(r["sites"])==0 and r["cap"]<length)
                            item=dict(status="inherited",rules=[rec])
                        else:
                            if monotonic()>=until:break
                            item=solver.solve(p,length,rules,old,folder,checker,
                                              min(args.seconds,max(.01,until-monotonic())),prev)
                            fixed.compact(folder,checker,trimmer,item)
                        rows[str(length)]=item
                        solver.joins.save_json(LEDGER,d)
                        print(root,k[:8],length,item["status"],flush=True)
        if args.replay:
            solver.joins.save_json(HERE/"individual-replay.json",dict(ledger=file_hash(LEDGER),
                                   reviewed={k:sorted(map(int,v)) for k,v in d["cases"].items()}))


if __name__=="__main__":main()
