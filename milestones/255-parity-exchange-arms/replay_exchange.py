"""Reconstruct the 96-edge completions by degree-two spanning cycles with one extra vertex."""
from collections import defaultdict
from hashlib import sha256
import json
from pathlib import Path
import subprocess
from tempfile import TemporaryDirectory

HERE = Path(__file__).resolve().parent
SOURCE = HERE.parent / "254-distant-arm-partners" / "parity-families.json"
SEED = "e6e522b8cb12744a1906938286731b33b0a5e5acfaff48a9e904ff3a1d14c102"
CSC = Path("C:/Windows/Microsoft.NET/Framework64/v4.0.30319/csc.exe")


def main():
    seed = set(json.loads(SOURCE.read_bytes())["shapes"][SEED][1::2])
    parity = next(iter(seed)).bit_count() % 2
    outside = {v for v in range(256) if v.bit_count() % 2 == parity} - seed
    expected = {(r, a) for r in seed for a in outside} | {(-1, -1)}
    if len(expected) != 3841:
        raise ValueError("Wrong number of parity classes")

    source = HERE / "replay_exchange.cs"
    with TemporaryDirectory(prefix="snake255-cycle-replay-") as tmp:
        exe = str(Path(tmp) / "replay.exe")
        subprocess.run([str(CSC), "/nologo", "/optimize+", "/out:" + exe, str(source)], check=True)
        result = subprocess.run([exe], input=",".join(map(str, sorted(seed))) + "\n",
                                text=True, capture_output=True, check=True)
    cases = {}
    paths = defaultdict(set)
    for line in result.stdout.splitlines():
        kind, r, a, *values = line.split()
        key = int(r), int(a)
        if key not in expected:
            raise ValueError("Unexpected parity class")
        if kind == "P":
            path = tuple(map(int, values[0].split(",")))
            vertices = seed if key == (-1, -1) else (seed - {key[0]}) | {key[1]}
            if (len(path) != 97 or len(set(path)) != 97 or set(path[1::2]) != vertices
                    or path[0] >= path[-1] or min(path) < 0 or max(path) > 255):
                raise ValueError("Incorrect labelled completion")
            for j, v in enumerate(path):
                if any(((v ^ path[i]).bit_count() == 1) != (i+1 == j) for i in range(j)):
                    raise ValueError("Incorrect induced adjacency")
            if path in paths[key]:
                raise ValueError("Duplicate labelled completion")
            paths[key].add(path)
        elif kind == "S":
            if key in cases:
                raise ValueError("Repeated parity class")
            cases[key] = tuple(map(int, values))
        else:
            raise ValueError("Unknown enumeration record")
    if cases.keys() != expected or any(n != len(paths[k]) for k, (_, n) in cases.items()):
        raise ValueError("Incomplete enumeration records")
    records = [dict(removed=r, added=a, spanning_cycles=cycles, paths=sorted(paths[r, a]))
               for (r, a), (cycles, _) in sorted(cases.items())]
    pins = {p.name: sha256(p.read_bytes()).hexdigest() for p in (SOURCE, source, Path(__file__), CSC)}
    output = dict(source_shape=SEED, source_side=sorted(seed), sha256=pins, classes=records)
    (HERE / "replay-exchange.json").write_text(json.dumps(output, separators=(",", ":")) + "\n",
                                               encoding="utf-8", newline="\n")
    print("Classes", len(cases), "nonempty", sum(bool(p) for p in paths.values()),
          "labelled completions", sum(map(len, paths.values())))


if __name__ == "__main__":
    main()
