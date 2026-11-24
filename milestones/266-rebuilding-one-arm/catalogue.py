"""Recover the rooted 93- to 95-edge arms of the archived one-crossing examples."""
from collections import Counter
from hashlib import sha256
from pathlib import Path
import gzip
import json
import sys

HERE = Path(__file__).resolve().parent
MS = HERE.parent
PREV = MS / "265-joint-arm-regrowth"
sys.path.insert(0, str(PREV))
from growth import checked


def read(path):
    return json.loads(path.read_bytes())


def write(path, data):
    path.write_bytes((json.dumps(data, separators=(",", ":")) + "\n").encode())


def label(arm):
    axes = list(dict.fromkeys(x ^ y for x, y in zip(arm, arm[1:])))
    assert len(axes) == 8
    lookup = [sum(1 << j for j, bit in enumerate(axes) if v & bit) for v in range(256)]
    return [lookup[v ^ arm[0]] for v in arm], lookup


def identifier(arm):
    return sha256(bytes(arm)).hexdigest()


def main():
    source = PREV / "exchange-states.json.gz"
    data = read(PREV / "exchange.json")
    assert sha256(source.read_bytes()).hexdigest() == data["states_sha256"]
    states = json.loads(gzip.decompress(source.read_bytes()))
    parents = {}
    for (left, right, _), origin in zip(states, data["starts"], strict=True):
        a, b = bytes.fromhex(left), bytes.fromhex(right)
        for arm, other in ((a,b),(b,a)):
            if not 93 <= len(arm)-1 <= 95:
                continue
            for reversed_arm in (False, True):
                parent, lut = label(arm[::-1] if reversed_arm else arm)
                key = identifier(parent)
                row = parents.setdefault(key, dict(parent=parent, retain_edges=len(parent)-1, from_191=False, partners={}))
                assert row["parent"] == parent
                if origin["name"].startswith("191-"):
                    row["from_191"] = True
                if not reversed_arm:
                    partner = [lut[v] for v in other]
                    assert checked(parent,partner)["edges"] == int(origin["name"].split("-")[0])
                    row["partners"][origin["name"]] = partner
    counts = Counter((r["retain_edges"], r["from_191"],max(map(len,r["partners"].values()),default=0)-1) for r in parents.values())
    print(sorted(counts.items()))
    write(HERE/"parents.json",dict(states_sha256=data["states_sha256"],parents=parents))

if __name__ == "__main__":
    main()
