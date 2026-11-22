"""Enumerate every 96-edge shape reachable in one step from a specified arm."""
from collections import Counter
from hashlib import sha256
from math import comb
from pathlib import Path
from tempfile import TemporaryDirectory
import json
import subprocess
import sys

HERE = Path(__file__).resolve().parent
MS = HERE.parent
sys.path.insert(0, str(MS / "256-two-exchange-parents"))
from enumerate_shell import read, search, word, check_path
from replay_exchange import CSC


def census(parent, radius, exe):
    base = set(parent[1::2])
    classes = []
    survivors = 0
    transcript = sha256()

    def record(removed, added, native=None):
        vertices = sorted((base-set(removed)) | set(added))
        paths, _ = search(vertices)
        if native is not None and Counter(paths) != Counter(native):
            raise ValueError("Contracted path and cycle solvers disagree")
        if paths:
            for path in paths:
                check_path(path)
                if len(path) != 97 or set(path[1::2]) != set(vertices):
                    raise ValueError("Incorrect parity class")
            classes.append(dict(removed=removed, inserted=added, paths=[
                dict(shape=sha256(word(p)).hexdigest(), vertices=p) for p in sorted(paths)]))

    if radius == 0:
        record([], [])
        survivors = 1
    else:
        raw = subprocess.run([str(exe), str(radius)], input=",".join(map(str, sorted(base)))+"\n",
                             text=True, capture_output=True, check=True)
        completions = None
        totals = None
        for line in raw.stdout.splitlines():
            kind, *fields = line.split()
            if kind == "T":
                totals = tuple(map(int, fields))
                continue
            if int(fields[0]) != survivors: raise ValueError("Candidate order")
            if kind == "C":
                if completions is not None: raise ValueError("Unfinished candidate")
                removed, added = [list(map(int, a.split(","))) for a in fields[1:]]
                transcript.update(bytes(removed+added))
                completions = []
            elif kind == "P":
                p = tuple(map(int, fields[2].split(",")))
                completions.append(min(p, p[::-1]))
            elif kind == "S":
                if int(fields[-1]) != len(completions): raise ValueError("Incomplete path list")
                record(removed, added, completions)
                survivors += 1
                completions = None
            else: raise ValueError(kind)
        if completions is not None or totals != (comb(48,radius), survivors):
            raise ValueError("Incomplete shells")
    return dict(radius=radius, reference=parent, candidate_sets=comb(48,radius)*comb(80,radius),
                supply_survivors=survivors, survivor_digest=transcript.hexdigest(), positive_classes=classes)


if __name__ == "__main__":
    source = Path(sys.argv[1]).resolve()
    key = sys.argv[2]
    parent = read(source)["shapes"][key]
    check_path(parent)
    if sha256(word(parent)).hexdigest() != key: raise ValueError("Incorrect source shape")
    cs = [MS / "255-parity-exchange-arms/replay_exchange.cs", MS / "256-two-exchange-parents/EnumerateExchanges.cs"]
    with TemporaryDirectory() as tmp:
        exe = Path(tmp) / "search.exe"
        subprocess.run([str(CSC), "/nologo", "/optimize+", "/main:EnumerateExchanges", "/out:"+str(exe),
                        *map(str,cs)], check=True, capture_output=True)
        for radius in range(5):
            row = census(parent, radius, exe)
            row["shapes"] = {r["shape"]:r["vertices"] for c in row["positive_classes"] for r in c["paths"]}
            row["inputs"] = {f.relative_to(MS).as_posix():sha256(f.read_bytes()).hexdigest()
                             for f in [source, *cs, Path(__file__), MS/"255-parity-exchange-arms/enumerate_arms.py"]}
            out = HERE / ("shell-"+key[:12]+"-"+str(radius)+".json")
            out.write_text(json.dumps(row, separators=(",",":"))+"\n",encoding="utf-8",newline="\n")
            print(key[:12], radius, row["supply_survivors"], len(row["positive_classes"]),len(row["shapes"]),flush=True)
