"""Apply the first three checked rooted exclusions to the two related parents."""
import hashlib
import json
from pathlib import Path

import fixed


SOURCES = (("6f8ef24c-161", 94), ("6f8ef24c-67", 95), ("bac52b55-67", 95))
HERE = Path(__file__).resolve().parent
base_sources = fixed.sources
base_bounds = fixed.bounds
base_save = fixed.p.joins.save_json
known = {}


def sources():
    old, pins, cases = base_sources()
    fixed_result = fixed.read(HERE / "sat-caps.json")
    fixed.require(fixed_result["pins"] == pins, "Fixed-root dependencies differ")
    inputs = {}
    for tag, length in SOURCES:
        _, _, parent, _ = cases[tag]
        source = fixed_result["roots"][tag]
        row, = [a for a in source["attempts"] if a["length"] == length]
        fixed.require(source["parent"] == parent and row["status"] == "excluded"
                      and fixed.file_hash(HERE/row["proof"]) == row["compressed"],
                      "Sibling source differs from the certified exclusion")
        # For a second parent R at the same vertex, every path longer than this
        # cap must hit the vertices blocked by the source parent and freed by R.
        old["254/" + tag, 0] = (parent, length - 1)
        known[tuple(parent)] = length - 1
        inputs[tag] = row
    pins["sibling.py"] = fixed.file_hash(Path(__file__))
    pins["selected_fixed_claims"] = hashlib.sha256(
        json.dumps(inputs, sort_keys=True, separators=(",", ":")).encode()).hexdigest()
    return old, pins, cases


def combined_bounds(row):
    lower, upper = base_bounds(row)
    upper = min(upper, known.get(tuple(row["parent"]), upper))
    fixed.require(lower <= upper, "Sibling claims contradict the witness")
    return lower, upper


def save(path, data):
    if path == HERE / "sat-replay.json":
        path = HERE / "sibling-replay.json"
    return base_save(path, data)


if __name__ == "__main__":
    fixed.sources = sources
    fixed.bounds = combined_bounds
    fixed.POOL = HERE / "sibling-caps.json"
    fixed.p.joins.save_json = save
    fixed.main()
