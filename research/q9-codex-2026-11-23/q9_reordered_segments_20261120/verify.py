"""Independent pairwise Q9 path audit and coordinate-symmetry classification."""
from collections import Counter
from pathlib import Path
import json

root = Path(__file__).resolve().parent


def canon(word):
    def first_seen(seq):
        labels = {}
        return "".join(str(labels.setdefault(axis, len(labels))) for axis in seq)
    return min(first_seen(word), first_seen(word[::-1]))


def verified_word(path):
    assert len(path) == len(set(path)) and all(0 <= x < 512 for x in path)
    for j, vertex in enumerate(path):
        for i in range(j):
            assert ((vertex ^ path[i]).bit_count() == 1) == (i + 1 == j)
    return canon("".join(str((x ^ y).bit_length() - 1) for x, y in zip(path, path[1:])))


def path_after(line):
    return list(map(int, line.split(" vertices ")[1].split()))


refs = set((root / "reference191.words").read_text().split())
assert len(refs) == 131
trims = {canon(t) for w in refs for t in (w[1:], w[:-1])}
mothers = set((root.parent / "q9_fresh_mother_lifts_20261120/q8_base726_all20.words").read_text().split())
control = next(line for line in (root / "control.log").read_text().splitlines() if line.startswith("FOUND"))
control_word = verified_word(path_after(control))
assert len(control_word) == 191 and control_word in refs
assert control_word == verified_word(list(map(int, (root / "control_input.vertices").read_text().split())))
report = {"ref191": len(refs), "truncated_ref190": len(trims), "Q8_mother_catalogue": len(mothers), "positive_control_edges": len(control_word)}
for filename in ("near800_deep.log", "free_terminals.log"):
    counts = Counter()
    seen = set()
    lines = (root / filename).read_text().splitlines()
    for line in lines:
        if not line.startswith("VALID "):
            continue
        w = verified_word(path_after(line))
        assert len(w) == int(line.split()[1]) and w not in seen
        seen.add(w)
        matches = any(len(set(sub)) <= 8 and canon(sub) in mothers
                      for i in range(len(w) - 95) for sub in [w[i:i + 96]])
        ref = w in (refs if len(w) == 191 else trims)
        counts[(len(w), ref, matches)] += 1
    assert lines[-1].startswith("DONE ")
    report[filename] = {"counts": [{"edges": k[0], "from_ref_or_its_trim": k[1],
                                    "contains_catalogued_96": k[2], "classes": n}
                                    for k, n in sorted(counts.items())], "native_summary": lines[-1]}
print(json.dumps(report, indent=2))
