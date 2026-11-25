"""Seek a 97-edge partner for a 94-edge arm of an archived 190-edge snake."""
from argparse import ArgumentParser
from pathlib import Path
from tempfile import TemporaryDirectory
import sys

HERE = Path(__file__).resolve().parent
LAST = HERE.parent / "266-rebuilding-one-arm"
sys.path.insert(0, str(LAST))
from align import bank, pack
from catalogue import read, write
import rebuild

base_model = rebuild.model


def family_model(parents):
    def encode(blocked, length, prefix, cycles, seen):
        cnf, chosen = base_model(blocked, length, prefix, cycles, seen)
        if len(parents) > 1:
            choices = []
            for sites in parents:
                select = cnf.variable()
                choices.append(select)
                cnf.clauses.extend([-select, -chosen[v]] for v in sorted(sites - blocked))
            cnf.clauses.append(choices)
        return cnf, chosen
    return encode


def roots():
    return {k:r for k,r in read(LAST / "parents.json")["parents"].items()
            if r["retain_edges"] == 94 and not r["from_191"]}


def plan():
    cases = roots()
    images = list(bank.permutation_images())
    groups = pack({k:r["parent"] for k,r in cases.items()}, images, 88)
    write(HERE/"groups.json", groups)
    print("Group sizes", [(len(g["ranks"]),len(g["blocked"])) for g in groups], flush=True)


def aligned(group, source, images):
    return {k:list(bytes(source[k]["parent"]).translate(images[p])) for k,p in group["ranks"].items()}


def query(group, source, images, args, tmp, tools, previous):
    parents = aligned(group, source, images)
    sites = [set(path[1:]) for path in parents.values()]
    common = set.intersection(*sites)
    assert sorted(common) == group["blocked"]
    rebuild.model = family_model(sites)
    result = rebuild.solve(HERE,tmp,tools,common,args.length,[0],previous.get("cycles",[]),[],args.seconds)
    if result["status"] == "witness":
        partner = result["path"]
        result["joined"] = {}
        for k,p in parents.items():
            if set(p).intersection(partner) == {0}:
                path = p[::-1] + [256+v for v in partner]
                rebuild.geometry.verify(path,9)
                result["joined"][k] = path
        assert result["joined"]
    return result


def main():
    ap = ArgumentParser()
    ap.add_argument("--plan", action="store_true")
    ap.add_argument("--seconds", type=float, default=5)
    ap.add_argument("--length", type=int, default=97)
    ap.add_argument("--only", type=int, nargs="+")
    args = ap.parse_args()
    if args.plan:
        plan()
        return
    groups = read(HERE/"groups.json")
    source, images = roots(), list(bank.permutation_images())
    dest = HERE/("queries-" + str(args.length) + ".json")
    ledger = read(dest) if dest.exists() else {}
    with TemporaryDirectory() as folder:
        tmp = Path(folder)
        tools = rebuild.masks.compilers(tmp)
        for i,g in enumerate(groups):
            old = ledger.get(str(i), {})
            if old.get("status") in ("excluded","witness") or args.only and i not in args.only:
                continue
            ans = query(g,source,images,args,tmp,tools,old)
            ledger[str(i)] = ans
            write(dest,ledger)
            print(i,len(g["ranks"]),args.length,ans["status"],flush=True)
            if ans["status"] == "witness" and args.length >= 97:
                return

if __name__ == "__main__":
    main()
