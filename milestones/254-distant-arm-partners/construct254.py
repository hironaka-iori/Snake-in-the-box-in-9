"""Reroute endpoint blockers and enumerate continuations of fixed seed prefixes."""
from hashlib import sha256
import json
from pathlib import Path
import subprocess
import sys
from tempfile import TemporaryDirectory

HERE = Path(__file__).resolve().parent
OLD = HERE.parent / "253-repeated-segment-growth"
PREV = HERE.parent / "252-shorter-reference-segments"
sys.path.insert(0, str(PREV))
from construct import ALL, NEIGHBOURS, check_join, path_mask

SOURCE = HERE / "PartnerGrowth.cs"
RECEIPT = HERE / "constructive.json"
COMPILER = Path("C:/Windows/Microsoft.NET/Framework64/v4.0.30319/csc.exe")


def read(path):
    return json.loads(path.read_bytes())


def digest(path):
    return sha256(path.read_bytes()).hexdigest()


def frozen_tree(parent, prefix):
    """Independently count all continuations by deleting each departing tip's neighborhood."""
    available = ALL & ~path_mask(parent)
    for v in prefix[:-1]:
        available &= ~((1 << v) | NEIGHBOURS[v])

    def visit(tip, free):
        count, height = 1, 0
        choices = NEIGHBOURS[tip] & free
        child_free = free & ~(NEIGHBOURS[tip] | (1 << tip))
        while choices:
            bit = choices & -choices
            choices -= bit
            child_count, child_height = visit(bit.bit_length() - 1, child_free)
            count += child_count
            height = max(height, 1 + child_height)
        return count, height

    count, height = visit(prefix[-1], available)
    return count, height + len(prefix) - 1


def endpoint_obstacles(parent, seed):
    result = []
    for axis in range(8):
        v = seed[-1] ^ (1 << axis)
        result.append(dict(axis=axis, vertex=v, in_parent=v in parent,
                           blocking_prior_positions=[i for i, w in enumerate(seed[:-1])
                                                     if (v ^ w).bit_count() <= 1]))
    return result


def solve(exe, record, original, salt):
    seq = original[::-1] if record["end"] else original
    root = seq[0]
    parent = [v ^ root for v in seq]
    seed = record["partner"]
    if record["root"] != root or check_join(parent, seed)["joined"] != record["joined"]:
        raise ValueError("The previous constructive witness disagrees with its rooted parent")
    input_paths = "".join(",".join(map(str, arm)) + "\n" for arm in (parent, seed))
    lines = subprocess.run([str(exe), str(salt)], input=input_paths, capture_output=True,
                           text=True, check=True, timeout=200).stdout.splitlines()
    result = dict(id=record["id"], end=record["end"], root=root, random_seed=salt,
                  initial_partner_edges=len(seed)-1, initial_tip=seed[-1],
                  initial_obstacles=endpoint_obstacles(parent, seed), prefixes=[])
    for line in lines:
        stage, a, b, c, raw = line.split()
        witness = [int(x) for x in raw.split(",")]
        checked = check_join(parent, witness)
        a, b, c = map(int, (a, b, c))
        if stage == "prefix":
            if witness[:a+1] != seed[:a+1]:
                raise ValueError("Changed the fixed prefix")
            row = dict(frozen_edges=a, visited=b, complete=bool(c),
                       partner_edges=len(witness)-1, partner=witness)
            if c:
                nodes, edges = frozen_tree(parent, seed[:a+1])
                if nodes != b or edges != len(witness)-1:
                    raise ValueError("Independent prefix enumeration disagrees")
                row["independent_count_and_maximum"] = [nodes, edges]
            result["prefixes"].append(row)
        elif stage == "unblock":
            result["targeted_reroutes"] = dict(attempts=a, visited=b, successes=c,
                                                best_partner=witness, partner_edges=len(witness)-1)
        elif stage == "regrowth":
            result["interior_regrowth"] = dict(attempts=1000, completed_bridges=a,
                                                bridge_nodes=b, tail_nodes=c)
            result.update(checked)
        else:
            raise ValueError(stage)
    if len(result["prefixes"]) != 7 or "all_pairs" not in result or "targeted_reroutes" not in result:
        raise ValueError("The worker did not report all stages")
    return result


def main():
    old_receipt = OLD / "remote-arms.json"
    closure = OLD / "closure.json"
    pins = {p.name: digest(p) for p in (old_receipt, closure, SOURCE, Path(__file__),
            PREV / "construct.py", HERE.parent / "251-eighty-edge-segments" / "bank_capacity.py")}
    all_cases = read(old_receipt)["cases"]
    shapes = read(closure)["paths"]
    cases = sorted((r for r in all_cases if r["id"].startswith(("6f8ef24c", "bac52b55"))),
                   key=lambda r: (r["id"], -r["end"]))
    selected = sys.argv[1:]
    keys = [r["id"][:8] + "-" + str(r["root"]) for r in cases]
    if set(selected) - set(keys):
        raise ValueError("Unknown root selection")
    data = read(RECEIPT) if RECEIPT.exists() else dict(pins=pins, cases={})
    if pins != data["pins"]:
        raise ValueError("Inputs changed since the saved runs")
    with TemporaryDirectory() as folder:
        exe = Path(folder) / "PartnerGrowth.exe"
        subprocess.run([str(COMPILER), "/nologo", "/optimize+", "/out:"+str(exe), str(SOURCE)],
                       capture_output=True, check=True)
        for index, (key, r) in enumerate(zip(keys, cases)):
            if selected and key not in selected:
                continue
            row = solve(exe, r, shapes[r["id"]], 25401+index)
            data["cases"][key] = row
            temp = RECEIPT.with_suffix(".tmp")
            temp.write_text(json.dumps(data, indent=2)+"\n", encoding="utf-8", newline="\n")
            temp.replace(RECEIPT)
            print(key, row["initial_partner_edges"], row["partner_edges"], row["joined_edges"],
                  [(p["frozen_edges"],p["partner_edges"]) for p in row["prefixes"] if p["complete"]],
                  flush=True)


if __name__ == "__main__":
    main()
