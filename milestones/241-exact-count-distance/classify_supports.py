"""Exterior inverse evaluations on the six four-block geometries (exact integers)."""
from hashlib import sha256
from itertools import combinations_with_replacement
from pathlib import Path
import json
import sys

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent / "240-five-count-recovery" / "scripts"))
from native_resources import snapshot


def examine(sizes):
    masks = []
    offset = 0
    for size in sizes:
        masks.append(((1 << size) - 1) << offset)
        offset += size
    # Fix the last block, then choose the even member of each antipodal pair.
    group = []
    for i in range(8):
        p = sum(mask for j, mask in enumerate(masks[:3]) if i & (1 << j))
        group.append(p ^ (511 if p.bit_count() % 2 else 0))
    neighbourhood = {p ^ (1 << j) for p in group for j in range(9)}
    rho = (0, 35, 0, -10, 0, 8, 0, -16, 0, 128)
    maxima = []
    for character in range(8):
        image = [sum((-1)**((character & i).bit_count()) * rho[(x ^ p).bit_count()]
                     for i, p in enumerate(group)) for x in range(512)]
        maxima.append(max(abs(v) for x, v in enumerate(image) if x not in neighbourhood))
    return dict(block_sizes=sizes, positions=group, exterior_maxima=maxima)


if __name__ == "__main__":
    gate = snapshot()
    if gate["processes"] or gate["errors"] or gate["free_bytes"] < 1024**3:
        raise RuntimeError(("Resource gate", gate))
    rows = [examine(tuple(reversed(sizes))) for sizes in combinations_with_replacement(range(1, 7), 4)
            if sum(sizes) == 9]
    receipt = dict(inverse_numerator_by_distance=[0,35,0,-10,0,8,0,-16,0,128],
                   source_sha256=sha256(Path(__file__).read_bytes()).hexdigest(), rows=rows)
    (HERE / "four-block-certificate.json").write_text(json.dumps(receipt, indent=2) + "\n",
                                                      encoding="utf-8", newline="\n")
    for row in rows:
        print(row["block_sizes"], row["exterior_maxima"])
