"""Recompute all long Q8 completions by independently growing and pairing two arms."""
from argparse import ArgumentParser
from hashlib import sha256
import json
from pathlib import Path
import subprocess
from tempfile import TemporaryDirectory

HERE = Path(__file__).resolve().parent
DONORS = HERE.parent / "248-rooted-arm-capacity" / "parents.json"
CORNERS = HERE.parent / "249-long-parent-joins" / "geometry.json"
COMPILER = Path("C:/Windows/Microsoft.NET/Framework64/v4.0.30319/csc.exe")


def digest(path):
    return sha256(path.read_bytes()).hexdigest()


def check_path(path):
    if len(set(path)) != len(path) or any(not 0 <= x < 256 for x in path):
        raise ValueError("Invalid vertices in Q8")
    for j, v in enumerate(path):
        for i in range(j):
            if ((v ^ path[i]).bit_count() == 1) != (j-i == 1):
                raise ValueError("Induced adjacency failed")


def word(path):
    letters = tuple(a ^ b for a, b in zip(path, path[1:]))
    def key(steps):
        order = {letter: i for i, letter in enumerate(dict.fromkeys(steps))}
        return bytes(order[t] for t in steps)
    return min(key(letters), key(letters[::-1]))


def main():
    cli = ArgumentParser(description=__doc__)
    cli.add_argument("--core", required=True, type=int)
    cli.add_argument("--start", type=int, default=0)
    cli.add_argument("--end", type=int, help="exclusive segment index")
    cli.add_argument("--combine", action="store_true", help="join an exact cover of disjoint saved slices")
    args = cli.parse_args()
    k = args.core
    census = HERE / f"census-{k}.json"
    native = HERE / "ReplayCore.cs"
    sources = [Path(__file__), native, DONORS, CORNERS, COMPILER, census]
    pins = {p.name: digest(p) for p in sources}
    data = json.loads(census.read_bytes())
    refs = [row["path"] for row in json.loads(DONORS.read_bytes())["rows"]]
    refs += [row["path"] for row in json.loads(CORNERS.read_bytes())["corner_closure"]["new_shapes"]]
    if len(refs) != 22 or len({word(path) for path in refs}) != 22:
        raise ValueError("Unexpected reference set")
    seeds = {}
    for path in refs:
        check_path(path)
        for i in range(len(path)-k):
            sub = path[i:i+k+1]
            seeds.setdefault(word(sub), sub)
    if data["core"] != k or data["segment_classes"] != len(seeds):
        raise ValueError("Core inventory differs")
    ids = sorted(seeds)
    end = len(ids) if args.end is None else args.end
    if not 0 <= args.start < end <= len(ids):
        raise ValueError("Interval outside seed inventory")
    checked = {}
    paths = {}
    if args.combine:
        if args.start != 0 or end != len(ids):
            raise ValueError("Only full assembly supported")
        for file in sorted(HERE.glob(f"replay-core-{k}-slice-*.json")):
            r = json.loads(file.read_bytes())
            if r["pins"] != pins:
                raise ValueError("Slice version mismatch")
            for item in r["cores"]:
                i = item["index"]
                if i in checked:
                    raise ValueError("Duplicate coverage")
                checked[i] = item
            paths.update(r["class_paths"])
    else:
        rows = "".join(f"{i} " + ",".join(map(str,seeds[ids[i]])) + "\n"
                       for i in range(args.start, end))
        with TemporaryDirectory(prefix="snake252-arms-") as folder:
            exe = Path(folder)/"ReplayCore.exe"
            subprocess.run([str(COMPILER),"/nologo","/optimize+","/out:"+str(exe),str(native)],check=True)
            run = subprocess.run([str(exe)],input=rows,capture_output=True,text=True,check=True)
        for line in run.stdout.splitlines():
            fields = line.split()
            if fields[0] == "P":
                _, spelling, csv = fields
                path = list(map(int,csv.split(",")))
                code = word(path)
                check_path(path)
                if not 96 <= len(code) <= 98 or bytes(map(int,spelling)) != code:
                    raise ValueError("Completion word disagrees with path")
                if not any(word(path[i:i+k+1]) in seeds for i in range(len(path)-k)):
                    raise ValueError("Completion lacks a reference segment")
                id_ = sha256(code).hexdigest()
                if id_ in paths:
                    raise ValueError("Duplicate native class")
                paths[id_] = path
            elif fields[0] == "C":
                i, short, long, fits = map(int,fields[1:])
                if i in checked:
                    raise ValueError("Duplicate native core")
                checked[i] = dict(index=i,word_sha256=sha256(ids[i]).hexdigest(),
                                  short_nodes=short,long_nodes=long,compatible_pairs=fits)
            else:
                raise ValueError("Unexpected native output")
    if set(checked) != set(range(args.start,end)) or any(
            r["word_sha256"] != sha256(ids[i]).hexdigest() for i,r in checked.items()):
        raise ValueError("Missing or mismatched seed")
    full = args.start == 0 and end == len(ids)
    if full:
        archived = data["all_ids"]
        if (len(archived) != data["total_classes"] or len(archived) != len(set(archived))
                or set(paths) != set(archived)):
            raise ValueError(("Final class mismatch",sorted(set(paths)-set(archived)),sorted(set(archived)-set(paths))))
        for row in data["new_shapes"]:
            check_path(row["path"])
            id_ = sha256(word(row["path"])).hexdigest()
            if id_ != row["id"] or id_ not in paths or row["edges"] != len(row["path"])-1:
                raise ValueError("Incorrect primary class representative")
    tag = "" if full else f"-slice-{args.start}-{end}"
    result = dict(core=k, pins=pins, full_coverage=full, seed_interval=[args.start,end],
                  segment_classes=len(seeds), total_classes=len(paths), class_paths=dict(sorted(paths.items())),
                  cores=[checked[i] for i in sorted(checked)])
    target = HERE / f"replay-core-{k}{tag}.json"
    target.write_text(json.dumps(result,separators=(",",":"))+"\n",encoding="utf-8",newline="\n")
    print(f"Independent two-arm enumeration: {len(checked)} segments, {len(paths)} long classes, full={full}")


if __name__ == "__main__":
    main()
