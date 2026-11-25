"""Account for all edits since the previous full written-source review and its addendum."""
from argparse import ArgumentParser
from collections import Counter
from hashlib import sha256
from pathlib import Path
import json
import re
import subprocess

BASE = "0706f423cdbb9344303c1ad795afa99506db45fa"
HERE = Path(__file__).resolve().parent

def git(root, *args):
    return subprocess.run(["git", *args], cwd=root, capture_output=True, check=True).stdout

def line_span(first, size):
    size = int(size) if size else 1
    start = int(first) - (1 if size else 0)
    return start, start + size

def compare(root, name, snapshot, prior):
    path = "paper/" + name + ".tex"
    old = git(root, "show", BASE + ":" + path)
    new = git(root, "show", snapshot + ":" + path) if snapshot else (root/path).read_bytes()
    before, after = (v.decode("utf-8-sig").splitlines() for v in (old, new))
    base_hash, current_hash = (sha256(v).hexdigest() for v in (old, new))
    if base_hash != prior[name]["reviewed_sha256"]:
        raise ValueError("The baseline does not match the previous reading record")
    versions = [BASE, snapshot] if snapshot else [BASE]
    patch = git(root, "diff", "--no-ext-diff", "--no-color", "--unified=0", *versions, "--", path)
    header = r"(?m)^@@ -(\d+)(?:,(\d+))? \+(\d+)(?:,(\d+))? @@"
    edits = []
    left = right = same = 0
    for a, b, c, d in re.findall(header, patch.decode("utf-8")):
        i, j = line_span(a, b)
        k, l = line_span(c, d)
        assert before[left:i] == after[right:k]
        same += i - left
        edits.append(dict(baseline=[i,j], reviewed=[k,l]))
        left, right = j, l
    assert before[left:] == after[right:]
    same += len(before) - left
    body = "\n".join(after)
    labels = Counter(re.findall(r"\\label\{([^}]+)\}", body))
    items = Counter(re.findall(r"\\bibitem(?:\[[^\]]+\])?\{([^}]+)\}", body))
    refs = set(re.findall(r"\\(?:eqref|pageref|autoref|ref)\{([^}]+)\}", body))
    cites = {k.strip() for s in re.findall(r"\\cite(?:\[[^\]]+\])?\{([^}]+)\}", body) for k in s.split(",")}
    assert refs <= labels.keys() and cites <= items.keys()
    assert max(labels.values(), default=0) <= 1 and max(items.values(), default=0) <= 1
    return dict(baseline_revision=BASE, baseline_sha256=base_hash, reviewed_sha256=current_hash,
                baseline_lines=len(before), reviewed_lines=len(after), unchanged_lines=same,
                added_or_replaced_lines=len(after)-same, removed_or_replaced_lines=len(before)-same,
                ref_labels=len(labels), bibliography_keys=len(items), edits_zero_based_half_open=edits)

if __name__ == "__main__":
    parser = ArgumentParser()
    parser.add_argument("--root", type=Path, default=HERE.parents[2])
    parser.add_argument("--snapshot", help="compare a saved revision, default to current sources")
    parser.add_argument("--output", type=Path, default=HERE/"source-coverage.json")
    args = parser.parse_args()
    prior = json.loads((args.root/"milestones/260-donor-intersections/review/source-coverage.json").read_bytes())
    results = {name: compare(args.root, name, args.snapshot, prior) for name in prior}
    args.output.write_text(json.dumps(results, indent=2)+"\n", encoding="utf-8", newline="\n")
    for name, r in results.items():
        print(name, r["unchanged_lines"], r["added_or_replaced_lines"], r["reviewed_lines"])
