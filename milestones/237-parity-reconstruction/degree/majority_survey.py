"""Seek a 192-edge Q9 snake retaining exactly 95 vertices of a saved majority class."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import sys
from time import monotonic
from zipfile import ZIP_DEFLATED, ZipFile

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
for variable in ("OMP_NUM_THREADS", "OPENBLAS_NUM_THREADS", "MKL_NUM_THREADS", "NUMEXPR_NUM_THREADS"):
    os.environ[variable] = "1"
sys.path.insert(0, str(ROOT / "work/solver_packages"))
import ortools
from ortools.sat.python import cp_model

BASE_FILE = ROOT / "milestones/236-parity-exchange-frontier/data/bases.json"
NEIGHBOURS = [[v ^ (1 << j) for j in range(9)] for v in range(512)]


def digest(data):
    return hashlib.sha256(data).hexdigest()


def connected_parts(selected):
    adjacent = {v: selected.intersection(NEIGHBOURS[v]) for v in selected}
    pending = set(selected)
    parts = []
    while pending:
        part = set()
        stack = [min(pending)]
        while stack:
            v = stack.pop()
            if v in pending:
                pending.remove(v)
                part.add(v)
                stack.extend(adjacent[v])
        parts.append(part)
    return adjacent, parts


def solve(base, budget, archive):
    seed = set(base["vertices"])
    parity = min(seed).bit_count() % 2
    major = [v for v in range(512) if v.bit_count() % 2 == parity]
    minor = [v ^ 1 for v in major]
    assert len(seed) == 96 and seed <= set(major)
    model = cp_model.CpModel()
    vertex = [model.new_bool_var(f"v{v}") for v in range(512)]
    end = {v: model.new_bool_var(f"e{v}") for v in major}
    model.add(sum(vertex[v] for v in sorted(seed)) == 95)
    model.add(sum(vertex[v] for v in major) == 97)
    model.add(sum(vertex[v] for v in minor) == 96)
    model.add(sum(end.values()) == 2)
    for v in major:
        model.add(end[v] <= vertex[v])
    for v, neighbours in enumerate(NEIGHBOURS):
        model.add(sum(vertex[w] for w in neighbours) + end.get(v, 0) == 2).only_enforce_if(vertex[v])
    result = dict(base=base["id"], iterations=[], status="UNKNOWN")
    start = monotonic()
    while monotonic() - start < budget:
        index = len(result["iterations"])
        filename = f'base{base["id"]:03d}-iteration{index}.pbtxt'
        content = str(model.proto).encode()
        archive.writestr(filename, content)
        solver = cp_model.CpSolver()
        solver.parameters.num_search_workers = 1
        solver.parameters.max_memory_in_mb = 256
        solver.parameters.linearization_level = 0
        solver.parameters.random_seed = 0
        solver.parameters.max_time_in_seconds = max(0.001, budget - (monotonic() - start))
        status = solver.solve(model)
        row = dict(model=filename, sha256=digest(content), status=solver.status_name(status),
                   elapsed=solver.wall_time, conflicts=solver.num_conflicts, branches=solver.num_branches)
        result["iterations"].append(row)
        if status not in (cp_model.FEASIBLE, cp_model.OPTIMAL):
            result["status"] = row["status"]
            break
        selected = {v for v in range(512) if solver.value(vertex[v])}
        ends = {v for v in major if solver.value(end[v])}
        adjacent, parts = connected_parts(selected)
        assert len(selected) == 193 and len(selected.intersection(major)) == 97
        assert len(selected & seed) == 95 and len(ends) == 2 and ends <= selected
        assert all(len(adjacent[v]) == 2 - int(v in ends) for v in selected)
        path_part, = [part for part in parts if part & ends]
        assert ends <= path_part
        cycles = [sorted(part) for part in parts if part.isdisjoint(ends)]
        row.update(selected=sorted(selected), endpoints=sorted(ends), cycles=cycles)
        if not cycles:
            path = [min(ends)]
            while len(path) < 193:
                choices = adjacent[path[-1]].difference(path[-2:])
                v, = choices
                path.append(v)
            assert set(path) == selected and path[-1] in ends
            assert all(((v ^ path[j]).bit_count() == 1) == (j == i + 1)
                       for i, v in enumerate(path) for j in range(i + 1, len(path)))
            result.update(status="WITNESS", path=path)
            break
        for cycle in cycles:
            model.add(sum(vertex[v] for v in cycle) < len(cycle))
    return result


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("label")
    parser.add_argument("--seconds-per-base", type=float, default=2.0)
    parser.add_argument("--bases", nargs="*", type=int)
    args = parser.parse_args()
    raw = BASE_FILE.read_bytes()
    source = json.loads(raw)
    assert all(digest(Path(path).read_bytes()) == expected for path, expected in source["pins"].items())
    bases = source["bases"]
    assert len(bases) == 145 and [b["id"] for b in bases] == list(range(145))
    ids = list(range(145)) if args.bases is None else args.bases
    assert len(set(ids)) == len(ids) and set(ids) <= set(range(145))
    report = dict(ortools=ortools.__version__, base_sha256=digest(raw), script_sha256=digest(Path(__file__).read_bytes()),
                  arguments=vars(args), results=[])
    destination = HERE / (args.label + ".json")
    assert not destination.exists()
    with ZipFile(HERE / (args.label + "-models.zip"), "x", ZIP_DEFLATED) as archive:
        for i in ids:
            result = solve(bases[i], args.seconds_per_base, archive)
            report["results"].append(result)
            destination.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
            print(i, result["status"], flush=True)


if __name__ == "__main__":
    main()
