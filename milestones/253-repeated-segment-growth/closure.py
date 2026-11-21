"""Enumerate repeated changes retaining 68 consecutive edges of a long cube path."""
from argparse import ArgumentParser
from collections import Counter
from hashlib import sha256
import json
from pathlib import Path
import subprocess
import sys
from tempfile import TemporaryDirectory

HERE = Path(__file__).resolve().parent
PRIOR = HERE.parent / "252-shorter-reference-segments"
sys.path.insert(0, str(PRIOR))
from census import COMPILER, audit, references, shape_id


def enumerate_closure(args):
    refs = references()
    selected = refs if args.donor is None else {args.donor: refs[args.donor]}
    paths = {shape_id(p): p for p in selected.values() if len(p)-1 >= args.floor}
    seeds = sorted(paths)
    layers = [seeds]
    expanded = set()
    windows = {}
    generations = []
    witness = {}
    old = json.loads((PRIOR / "census-68.json").read_bytes())
    native = PRIOR / "Grow.cs"
    with TemporaryDirectory(prefix="snake253-regrowth-") as name:
        temp = Path(name)
        exe, inp, out = (temp / n for n in ("Grow.exe", "segments", "paths"))
        subprocess.run([str(COMPILER), "/nologo", "/optimize+", "/out:"+str(exe), str(native)], check=True)
        while True:
            frontier = sorted(key for key,p in paths.items() if key not in expanded and len(p)-1 >= args.floor)
            if not frontier or len(frontier) > args.frontier_limit:
                break
            cores = []
            for key in frontier:
                p = paths[key]
                for i in range(len(p)-68):
                    q = p[i:i+69]
                    word = audit.key(q)
                    if word not in windows:
                        row = dict(parent=key, start=i, core_sha256=sha256(word).hexdigest())
                        windows[word] = row
                        cores.append((row,q))
            before = set(paths)
            counts = {}
            if cores:
                inp.write_text("".join(",".join(map(str,q))+"\n" for _,q in cores),encoding="ascii")
                subprocess.run([str(exe), str(inp), str(out)], check=True)
                with out.open() as lines:
                    for line in lines:
                        tag, index, payload = line.split(maxsplit=2)
                        j = int(index)
                        if tag == "C":
                            if j in counts: raise ValueError("Duplicate coverage")
                            counts[j] = int(payload)
                            continue
                        if tag != "P": raise ValueError("Unknown native record")
                        left, csv = payload.split()
                        p = list(map(int, csv.split(",")))
                        left = int(left)
                        row,q = cores[j]
                        if not 96 <= len(p)-1 <= 98 or p[left:left+69] != q:
                            raise ValueError("Completion lacks its central subpath")
                        key = shape_id(p)
                        if key not in paths:
                            audit.verify_path(p)
                            paths[key] = p
                            witness[key] = dict(parent=row["parent"], parent_start=row["start"], child_start=left)
            if set(counts) != set(range(len(cores))): raise ValueError("Incomplete enumeration")
            for j,(row,_) in enumerate(cores): row["nodes"] = counts[j]
            expanded.update(frontier)
            new = sorted(set(paths)-before)
            if new: layers.append(new)
            info = dict(expanded=len(frontier), fresh_segments=len(cores), nodes=sum(counts.values()),
                        new_by_length=dict(Counter(len(paths[k])-1 for k in new)))
            generations.append(info)
            print(len(generations),info,"total",len(paths),flush=True)
            if len(generations)==1 and args.floor==96 and args.donor is None and set(paths)!=set(old["all_ids"]):
                raise ValueError("First generation disagrees with the previous full census")
    pins = {p.name:audit.digest(p) for p in (Path(__file__),native,Path(audit.__file__),PRIOR/"census.py",
                                             PRIOR/"census-68.json",audit.INVENTORY,audit.GEOMETRY,COMPILER)}
    waiting = sorted(k for k,p in paths.items() if len(p)-1>=args.floor and k not in expanded)
    report = dict(core=68, minimum_intermediate=args.floor, seeds=seeds, paths=dict(sorted(paths.items())),
                  expanded=sorted(expanded), layers=layers, closed=not waiting, unexpanded=waiting,
                  generations=generations, windows=list(windows.values()), discovery=witness, pins=pins)
    (HERE/args.output).write_text(json.dumps(report,separators=(",",":"))+"\n",encoding="utf-8",newline="\n")
    print("closed",not waiting,"shapes",len(paths),"waiting",len(waiting),flush=True)


if __name__=="__main__":
    cli = ArgumentParser(description=__doc__)
    cli.add_argument("--floor",type=int,choices=(96,97,98),default=96)
    cli.add_argument("--donor")
    cli.add_argument("--frontier-limit",type=int,default=300)
    cli.add_argument("--output",default="closure.json")
    enumerate_closure(cli.parse_args())
