"""Delete a prescribed first edge from the candidate partner and solve in the translated cube."""
from argparse import ArgumentParser
from pathlib import Path
from tempfile import TemporaryDirectory
from search import HERE, aligned, roots, bank, read, write, rebuild, family_model
import search


def residual(parents, first):
    blocked = {0} | {1 << i for i in range(8) if 1 << i != first}
    return {k:{v ^ first for v in set(p[1:]) | blocked} for k,p in parents.items() if first not in p}


def main():
    parser = ArgumentParser()
    parser.add_argument("--seconds", type=float, default=4)
    parser.add_argument("--length", type=int, default=97)
    parser.add_argument("--only", type=int, nargs="+")
    parser.add_argument("--deficit", action="store_true")
    parser.add_argument("--published", action="store_true")
    args=parser.parse_args()
    if args.deficit:
        from deficit import model
        search.base_model=model
    groups=read(HERE/"groups.json")
    roots_query=read(HERE/f"queries-{args.length}.json")
    shorter_file=HERE/f"queries-{args.length-1}.json"
    shorter=read(shorter_file) if shorter_file.exists() else {}
    shorter_steps_file=HERE/f"steps-{args.length-1}.json"
    shorter_steps=read(shorter_steps_file) if shorter_steps_file.exists() else {}
    dest=HERE/f"steps-{args.length}.json"
    ledger=read(dest) if dest.exists() else {}
    source,images=roots(),list(bank.permutation_images())
    with TemporaryDirectory() as folder:
        tmp=Path(folder)
        tools=rebuild.masks.compilers(tmp)
        for i,g in enumerate(groups):
            if (roots_query.get(str(i),{}).get("status")=="excluded" or
                shorter.get(str(i),{}).get("status")=="excluded" or args.only and i not in args.only):
                continue
            if args.published and not any(source[k]["partners"] for k in g["ranks"]):
                continue
            parents=aligned(g,source,images)
            rows=ledger.setdefault(str(i),{})
            for first in (1 << j for j in range(8)):
                domains=residual(parents,first)
                old=rows.get(str(first),{})
                if not domains or old.get("status") in ("excluded","witness"):
                    continue
                if shorter_steps.get(str(i),{}).get(str(first),{}).get("status")=="excluded":
                    continue
                sites=list(domains.values())
                common=set.intersection(*sites)
                rebuild.model=family_model(sites)
                rec=rebuild.solve(HERE,tmp,tools,common,args.length-1,[0],old.get("cycles",[]),[],args.seconds)
                if args.deficit:
                    rec["encoding"]="parity-deficit"
                if rec["status"]=="witness":
                    partner=[0]+[v ^ first for v in rec["path"]]
                    rec["joined"]={}
                    for key,p in parents.items():
                        if set(p).intersection(partner)=={0}:
                            q=p[::-1]+[256+v for v in partner]
                            rebuild.geometry.verify(q,9)
                            rec["joined"][key]=q
                    assert rec["joined"]
                rows[str(first)]=rec
                write(dest,ledger)
                print(i,first,len(domains),rec["status"],flush=True)
                if rec["status"]=="witness" and args.length>=97:
                    return

if __name__=="__main__":
    main()
