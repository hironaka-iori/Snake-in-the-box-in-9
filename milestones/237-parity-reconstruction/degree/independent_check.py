"""Compare independent literal screenings, and decide each surviving Hamilton instance."""
from collections import Counter
from hashlib import sha256
from itertools import combinations
import json
import os
from pathlib import Path
import subprocess
import sys
from tempfile import TemporaryDirectory

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
BASES = ROOT / "milestones/236-parity-exchange-frontier/data/bases.json"
DECISIONS = HERE.parent / "majority/decisions.json"
for var in ("OMP_NUM_THREADS", "MKL_NUM_THREADS", "OPENBLAS_NUM_THREADS", "NUMEXPR_NUM_THREADS"):
    os.environ[var] = "1"
sys.path.insert(0, str(ROOT / "work/solver_packages"))
from ortools.sat.python import cp_model


def digest(path):
    return sha256(path.read_bytes()).hexdigest()


def circuit(vertices):
    # A pair of same-parity vertices at Hamming distance two has exactly two
    # common cube neighbours. Check each against all members of this fixed set.
    order = sorted(vertices)
    cube_neighbours = {z: {u for u in vertices if (z ^ u).bit_count() == 1} for z in range(512)}
    model = cp_model.CpModel()
    arcs = []
    def add(i, j):
        arcs.append((i, j, model.new_bool_var(f"{i}_{j}")))
        arcs.append((j, i, model.new_bool_var(f"{j}_{i}")))
    for (i, v), (j, w) in combinations(enumerate(order), 2):
        bits = v ^ w
        if bits.bit_count() != 2:
            continue
        low = bits & -bits
        if any(cube_neighbours[z] == {v,w} for z in (v ^ low, w ^ low)):
            add(i, j)
    dummy = len(order)
    for i in range(dummy):
        add(i, dummy)
    model.add_circuit(arcs)
    solver = cp_model.CpSolver()
    solver.parameters.num_search_workers = 1
    solver.parameters.max_time_in_seconds = 2
    solver.parameters.max_memory_in_mb = 256
    status = solver.solve(model)
    return solver.status_name(status)


def main():
    exe = Path(sys.argv[1]).resolve()
    bases = [set(row["vertices"]) for row in json.loads(BASES.read_bytes())["bases"]]
    stdin = "".join(f"{i} " + " ".join(map(str, sorted(s))) + "\n" for i,s in enumerate(bases))
    process = subprocess.run([str(exe)], input=stdin, capture_output=True, text=True, check=True)
    hits = [tuple(map(int, line.split())) for line in process.stdout.splitlines()]
    counts = [list(map(int, line.split())) for line in process.stderr.splitlines()]
    assert [r[0] for r in counts] == list(range(145))
    groups = json.loads(DECISIONS.read_bytes())
    archived = [tuple(r) for g in groups for r in g["descriptions"]]
    assert len(hits) == len(set(hits)) and sorted(hits) == sorted(archived)
    decisions = []
    for group in groups:
        sets = {frozenset((bases[i] - {d}) | {a,b}) for i,d,a,b in group["descriptions"]}
        assert len(sets) == 1
        vertices, = sets
        decisions.append(circuit(vertices))
    assert len({frozenset((bases[i] - {d}) | {a,b}) for i,d,a,b in hits}) == len(groups)
    report = dict(exact_input_descriptions=len(bases)*96*160*159//2, final_graphs_evaluated=sum(r[1] for r in counts),
                  surviving_descriptions=len(hits), distinct_graphs=len(groups), source= digest(HERE/"independent_screen.cpp"),
                  binary=digest(exe), check_script=digest(Path(__file__)), bases=digest(BASES),
                  archive=digest(DECISIONS), circuit_outcomes=dict(Counter(decisions)), per_group=decisions,
                  per_base=counts, solver_workers=1, solver_seconds_per_graph=2)
    (HERE/"independent-results.json").write_text(json.dumps(report, indent=2)+"\n", encoding="utf-8")
    print({k:v for k,v in report.items() if k not in ("per_group","per_base")})


if __name__ == "__main__":
    main()
