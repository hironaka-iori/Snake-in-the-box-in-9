"""Verify the two selections by direct Hamming-distance-one counting on Q9."""
from datetime import datetime, timezone
from hashlib import sha256
from pathlib import Path
import json
import sys


HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent / "240-five-count-recovery" / "scripts"))
from native_resources import snapshot


def antipodal_pair(bits, full):
    return int(bits == 0) - int(bits == full)


def selected_difference(x):
    low = x & 15
    if x & 256:
        five = -antipodal_pair(low, 15)
    else:
        five = int(low.bit_count() == 1) - int(low.bit_count() == 3)
    return five * antipodal_pair((x >> 4) & 3, 3) * antipodal_pair((x >> 6) & 3, 3)


def profile(selection):
    return [sum((x ^ y).bit_count() == 1 for y in selection) for x in range(512)]


if __name__ == "__main__":
    gate = snapshot()
    if gate["errors"] or gate["processes"] or gate["free_bytes"] < 1024**3:
        raise RuntimeError(("Resource gate", gate))
    plus = [x for x in range(512) if selected_difference(x) == 1]
    minus = [x for x in range(512) if selected_difference(x) == -1]
    expected = {0: 3, 15: -3, 48: -3, 63: 3, 192: -3, 207: 3, 240: 3, 255: -3}
    pos, neg = profile(plus), profile(minus)
    differences = {x: a - b for x, (a, b) in enumerate(zip(pos, neg)) if a != b}
    if (len(plus), len(minus)) != (20, 20) or differences != expected:
        raise ValueError((plus, minus, differences))
    if any(x.bit_count() % 2 != 1 for x in plus + minus):
        raise ValueError("A selected vertex has even parity")
    receipt = dict(status="verified", source_sha256=sha256(Path(__file__).read_bytes()).hexdigest(),
                   positive_selection=plus, negative_selection=minus,
                   differing_counts=differences, equal_counts=512-len(differences),
                   equal_even_side_counts=256-len(differences), vertices_evaluated=512,
                   comparison="Count distance-one neighbours in each explicit selection independently.",
                   started_free_bytes=gate["free_bytes"], finished_utc=datetime.now(timezone.utc).isoformat())
    (HERE / "witness.json").write_text(json.dumps(receipt, indent=2) + "\n", encoding="utf-8", newline="\n")
    print(differences)
