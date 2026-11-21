"""Verify repeated 68-edge growth with independent two-arm enumeration and reachability."""
from argparse import ArgumentParser
from collections import Counter, defaultdict
from hashlib import sha256
import json
from pathlib import Path
import subprocess
import sys
from tempfile import TemporaryDirectory

HERE = Path(__file__).resolve().parent
PREVIOUS = HERE.parent / "252-shorter-reference-segments"
sys.path.insert(0, str(PREVIOUS))
from replay_core import CORNERS, DONORS, COMPILER, check_path, digest, word

K = 68


def read(path):
    return json.loads(path.read_bytes())


def identifier(path):
    return sha256(word(path)).hexdigest()


def windows(path):
    for start in range(len(path)-K):
        segment = tuple(path[start:start+K+1])
        yield word(segment), segment


def native_growth(seeds, source):
    keys = sorted(seeds)
    rows = "".join(f"{i} " + ",".join(map(str, seeds[key])) + "\n"
                   for i, key in enumerate(keys))
    with TemporaryDirectory(prefix="snake253-replay-") as folder:
        exe = Path(folder) / "ReplayCore.exe"
        subprocess.run([str(COMPILER), "/nologo", "/optimize+", "/out:"+str(exe), str(source)],
                       capture_output=True, check=True)
        run = subprocess.run([str(exe)], input=rows, capture_output=True, text=True, check=True)
    coverage, found = {}, {}
    for line in run.stdout.splitlines():
        parts = line.split()
        if parts[0] == "P":
            _, spelling, csv = parts
            path = list(map(int, csv.split(",")))
            check_path(path)
            key = word(path)
            if len(key) not in (96,97,98) or key != bytes(map(int,spelling)):
                raise ValueError("Invalid completion or mismatched representative")
            if not any(s in seeds for s, _ in windows(path)):
                raise ValueError("Completion contains no enumerated segment")
            ident = identifier(path)
            if ident in found:
                raise ValueError("Repeated canonical completion")
            found[ident] = path
        elif parts[0] == "C":
            i, short, long, pairs = map(int, parts[1:])
            if i in coverage or not 0 <= i < len(keys):
                raise ValueError("Invalid enumerated core index")
            coverage[i] = dict(segment=sha256(keys[i]).hexdigest(), short_nodes=short,
                               long_nodes=long, compatible_pairs=pairs)
        else:
            raise ValueError("Unrecognized enumeration output")
    if set(coverage) != set(range(len(keys))):
        raise ValueError("Incomplete segment coverage")
    return found, [coverage[i] for i in sorted(coverage)]


def distances(paths, roots, expanded):
    # In the unrestricted growth operation each endpoint can be replaced.
    # Its adjacency is exactly incidence with an identical contiguous segment.
    by_segment = defaultdict(set)
    of_shape = {}
    for key, path in paths.items():
        of_shape[key] = {w for w,_ in windows(path)}
        for w in of_shape[key]:
            by_segment[w].add(key)
    layers, seen = [], set()
    frontier = set(roots)
    while frontier:
        layers.append(sorted(frontier))
        seen.update(frontier)
        subwords = {w for key in frontier & expanded for w in of_shape[key]}
        frontier = {key for w in subwords for key in by_segment[w]} - seen
    if seen != set(paths):
        raise ValueError("Terminal set includes an unreachable class")
    return layers, of_shape


def main():
    cli = ArgumentParser(description=__doc__)
    cli.add_argument("--source", default="closure.json")
    args = cli.parse_args()
    primary = HERE / args.source
    data = read(primary)
    floor = data["minimum_intermediate"]
    if data["core"] != K or floor not in (96,97,98):
        raise ValueError("Unexpected growth specification")
    sources = [r["path"] for r in read(DONORS)["rows"]]
    sources += [r["path"] for r in read(CORNERS)["corner_closure"]["new_shapes"]]
    for p in sources:
        check_path(p)
    if len(sources) != 22 or len({identifier(p) for p in sources}) != 22:
        raise ValueError("Unexpected original reference inventory")
    initial = {identifier(p) for p in sources if len(p)-1 >= floor}
    if len(initial) != len(data["seeds"]) or initial != set(data["seeds"]):
        raise ValueError("Seeds do not match the eligible original references")
    claimed = data["paths"]
    for ident, path in claimed.items():
        check_path(path)
        if not 96 <= len(path)-1 <= 98 or identifier(path) != ident:
            raise ValueError("Invalid recorded path or shape identifier")
    expanded = set(data["expanded"])
    eligible = {key for key,p in claimed.items() if len(p)-1 >= floor}
    if (len(expanded) != len(data["expanded"]) or not expanded <= eligible
            or not initial <= expanded or data["closed"] != (expanded == eligible)):
        raise ValueError("Expanded states, eligible states, and closure claim disagree")
    seeds = {}
    for key in sorted(expanded):
        for w, segment in windows(claimed[key]):
            seeds.setdefault(w, segment)
    native = PREVIOUS / "ReplayCore.cs"
    found, receipts = native_growth(seeds, native)
    if set(found) != set(claimed):
        raise ValueError(("Independent union census differs",
                          sorted(set(found)-set(claimed)), sorted(set(claimed)-set(found))))
    levels, all_words = distances(found, initial, expanded)
    expected = [sorted(layer) for layer in data["layers"]]
    if levels != expected:
        raise ValueError(("Independent incidence distances differ",
                          list(map(len, levels)), list(map(len, expected))))
    if set(seeds) != {w for key in expanded for w in all_words[key]}:
        raise ValueError("Native representatives changed the expanded segment inventory")
    files = [primary, Path(__file__), native, PREVIOUS/"replay_core.py", DONORS, CORNERS]
    result = dict(core=K,minimum_intermediate=floor,closed=data["closed"],
                  pins={p.relative_to(HERE.parent.parent).as_posix():digest(p) for p in files},
                  compiler_sha256=digest(COMPILER),initial_classes=len(initial),
                  expanded_classes=len(expanded),occupied_segments=len(seeds),
                  total_classes=len(found),lengths=dict(sorted(Counter(len(p)-1 for p in found.values()).items())),
                  all_ids=sorted(found),layers=levels,
                  pending_eligible=sorted(eligible-expanded),coverage=receipts)
    out = HERE / ("replay-"+primary.stem+".json")
    out.write_text(json.dumps(result,separators=(",",":"))+"\n",encoding="utf-8",newline="\n")
    print("Checked", len(seeds), "segments and", len(found), "long shapes; distance layers",
          list(map(len,levels)), "closed", data["closed"], flush=True)


if __name__=="__main__":
    main()
