"""Resume the original ten unrestricted partner queries, then replay their exclusions."""
from hashlib import sha256
from pathlib import Path
from tempfile import TemporaryDirectory
import json


HERE = Path(__file__).resolve().parent
PREV = HERE.parent / "246-eight-dimensional-parents"
SOURCE = HERE.parent / "243-coil-opening"


def main():
    destination = HERE / "partners.json"
    saved = destination.read_bytes()
    record = json.loads(saved)
    pins = record["pins"]
    paths = [HERE/"partner.py", PREV/"arm-structure.json", PREV/"comparison.json",
             PREV/"free_outer.py", SOURCE/"arc_sat.py"]
    if any(sha256(p.read_bytes()).hexdigest() != pins[p.name] for p in paths):
        raise ValueError("The original partner source or inputs have changed")
    original = json.loads((PREV/"ceiling.json").read_bytes())["pins"]
    if sha256((SOURCE/"open_coil.py").read_bytes()).hexdigest() != original["open_coil.py"]:
        raise ValueError("The inherited cube module has changed")
    import partner
    if (set(pins) != {p.name for p in paths} | {partner.SOLVER.name}
            or partner.digest(partner.SOLVER) != pins[partner.SOLVER.name]
            or pins[partner.SOLVER.name] != original[partner.SOLVER.name]):
        raise ValueError("The solver or set of pinned dependencies has changed")

    arms = partner.parent_arms()
    expected = [(i, e) for i in sorted(arms) for e in (0, 1)]
    if len(expected) != 10 or record["requested"] != len(expected):
        raise ValueError("The checkpoint is not the original ten-case survey")
    coverage = record["coverage"]
    if [(c["class_id"], c["endpoint"]) for c in coverage] != expected:
        raise ValueError("The saved case order has changed")
    for (i, e), c in zip(expected, coverage):
        parent = partner.rooted_parent(arms[i], e)
        if (c["rooted_parent"] != parent or c["requested_prefixes"] != [[0]]
                or c["next_vertices"] != partner.next_vertices(parent, [0])):
            raise ValueError(("Unrestricted parent case differs", i, e))
    rows = record["records"]
    done = [(r["class_id"], r["endpoint"]) for r in rows]
    if done != expected[:len(rows)] or record["pending"] != len(expected)-len(rows):
        raise ValueError("Incomplete or out-of-order original checkpoint")
    if any(r["prefix"] != [0] or r["seed"] != 0 or r["budget_seconds"] != 2
           or r["initial_cycles"] != [] for r in rows):
        raise ValueError("Checkpoint solver settings differ from the original run")

    with TemporaryDirectory(prefix="q8-partner-resume-") as tmp:
        for c in coverage[len(rows):]:
            if any(r["status"] == "witness" for r in rows):
                break
            result = partner.decide(c["rooted_parent"], [0], Path(tmp), seconds=2, seed=0)
            rows.append(dict(class_id=c["class_id"], endpoint=c["endpoint"], **result))
            record["pending"] = len(expected)-len(rows)
            updated = (json.dumps(record, separators=(",", ":"))+"\n").encode("utf-8")
            if destination.read_bytes() != saved:
                raise RuntimeError("Another process changed the partner checkpoint")
            temporary = destination.with_suffix(".resume.tmp")
            temporary.write_bytes(updated)
            temporary.replace(destination)
            saved = updated
            print("Arm", c["class_id"], "endpoint", c["endpoint"], result["status"], flush=True)
    import partner_replay
    partner_replay.main()


if __name__ == "__main__":
    main()
