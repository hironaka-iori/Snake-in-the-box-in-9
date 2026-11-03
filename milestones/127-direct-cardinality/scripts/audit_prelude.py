"""Independent read-only reconstruction and ordered RUP audit; no solver imports."""
from pathlib import Path
from itertools import combinations
from collections import Counter
import argparse
import datetime
import hashlib
import json
import time

HERE = Path(__file__).resolve().parents[1]
ROOT = HERE.parents[1]
PREVIOUS = ROOT / "milestones/125-critical-six-count"
PINS = {}


def digest(path):
    path = Path(path).resolve()
    h = hashlib.sha256()
    with path.open("rb") as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b""):
            h.update(block)
    result = h.hexdigest()
    name = path.relative_to(ROOT).as_posix()
    if name in PINS:
        assert PINS[name] == result, ("Input changed", name)
    PINS[name] = result
    return result


def read(path):
    digest(path)
    return json.loads(Path(path).read_text(encoding="utf-8-sig"))


def verify(path, expected):
    assert digest(path) == expected, ("Hash mismatch", str(path))


def parse_cnf(path):
    digest(path)
    clauses = []
    header = None
    with path.open("rt", encoding="ascii") as stream:
        for line in stream:
            tokens = line.split()
            if not tokens or tokens[0] == "c":
                continue
            if tokens[0] == "p":
                assert header is None and not clauses and tokens[:2] == ["p", "cnf"]
                assert len(tokens) == 4
                header = tuple(map(int, tokens[2:]))
                continue
            assert header is not None
            row = tuple(map(int, tokens))
            assert row and row[-1] == 0 and 0 not in row[:-1]
            assert all(0 < abs(lit) <= header[0] for lit in row[:-1])
            assert len(set(row[:-1])) == len(row) - 1
            assert not any(-lit in row[:-1] for lit in row[:-1])
            clauses.append(row[:-1])
    assert header is not None and len(clauses) == header[1]
    return header, clauses


def rebuild_formula(window, bounds, cuts, corners):
    """Independent procedural copy of the documented CNF, without producer imports."""
    clauses = []
    last_variable = 512

    def add(row):
        clauses.append(tuple(row))

    def at_most(literals, cap):
        nonlocal last_variable
        if cap >= len(literals):
            return
        assert 1 <= cap < len(literals)
        registers = []
        for _ in literals:
            registers.append(tuple(range(last_variable + 1, last_variable + cap + 1)))
            last_variable += cap
        add((-literals[0], registers[0][0]))
        for register in registers[0][1:]:
            add((-register,))
        for index in range(1, len(literals)):
            literal = literals[index]
            previous, current = registers[index - 1], registers[index]
            add((-literal, current[0]))
            add((-previous[0], current[0]))
            for column in range(1, cap):
                add((-literal, -previous[column - 1], current[column]))
                add((-previous[column], current[column]))
            add((-literal, -previous[-1]))

    for vertex in window:
        add((vertex + 1,))
    endpoint_flags = []
    for vertex in range(512):
        selected = vertex + 1
        neighbours = tuple((vertex ^ (1 << axis)) + 1 for axis in range(9))
        for triple in combinations(neighbours, 3):
            add((-selected, *(-n for n in triple)))
        last_variable += 1
        endpoint = last_variable
        endpoint_flags.append(endpoint)
        add((-selected, *neighbours))
        add((-endpoint, selected))
        for excluded in range(9):
            add((-selected, endpoint, *(n for i, n in enumerate(neighbours) if i != excluded)))
        for first, second in combinations(neighbours, 2):
            add((-endpoint, -first, -second))
    at_most(endpoint_flags, 2)
    for opposite, (lower, upper) in zip(corners, bounds, strict=True):
        if upper < 21:
            at_most([-(v + 1) for v in opposite], upper)
        if lower:
            at_most([v + 1 for v in opposite], 21 - lower)
    for vertex in range(512):
        for a, b in combinations(range(9), 2):
            if vertex & ((1 << a) | (1 << b)):
                continue
            face = (vertex, vertex | (1 << a), vertex | (1 << b), vertex | (1 << a) | (1 << b))
            add(tuple(-(v + 1) for v in face))
        for axes in combinations(range(9), 3):
            if vertex & sum(1 << a for a in axes):
                continue
            cube = tuple(vertex | sum((1 << axis) for bit, axis in enumerate(axes) if code & (1 << bit))
                         for code in range(8))
            for excluded in range(4):
                add(tuple(-(cube[i] + 1) for i in range(8) if i not in (excluded, 7 - excluded)))
    occurrences = sorted(-(v + 1) for opposite in corners for v in opposite)
    at_most(occurrences, 22)
    before_cuts = len(clauses)
    for cut in cuts:
        add(tuple(-(v + 1) for v in cut))
    return last_variable, clauses, before_cuts


def check_induced_cycle(vertices):
    selected = set(vertices)
    assert len(selected) == len(vertices) > 2 and all(0 <= v < 512 for v in selected)
    adjacency = {v: [v ^ (1 << a) for a in range(9) if (v ^ (1 << a)) in selected] for v in selected}
    assert all(len(neighbours) == 2 for neighbours in adjacency.values())
    reached, queue = set(), [next(iter(selected))]
    while queue:
        vertex = queue.pop()
        if vertex not in reached:
            reached.add(vertex)
            queue.extend(adjacency[vertex])
    assert reached == selected


def replay_original_only(clause, hints, original, variables):
    """Replay each ordered hint with a fresh three-valued assignment."""
    values = [0] * (variables + 1)
    for literal in clause:
        variable = abs(literal)
        required = -1 if literal > 0 else 1
        assert values[variable] in (0, required)
        values[variable] = required
    propagated = 0
    for offset, identifier in enumerate(hints):
        assert 1 <= identifier <= len(original), ("Non-original hint", identifier)
        unset = []
        for literal in original[identifier - 1]:
            value = values[abs(literal)] * (1 if literal > 0 else -1)
            assert value != 1, ("Satisfied clause supplied as a propagation hint", identifier)
            if value == 0:
                unset.append(literal)
        assert len(unset) <= 1, ("Hint is not unit or conflicting", identifier)
        if not unset:
            assert offset == len(hints) - 1, "Hints follow a completed contradiction"
            return propagated, identifier
        literal = unset[0]
        assert values[abs(literal)] == 0
        values[abs(literal)] = 1 if literal > 0 else -1
        propagated += 1
    raise AssertionError("No final contradiction")


def audit():
    start = time.monotonic()
    meta = read(HERE / "data/prelude.json")
    data = read(HERE / "data/direct-clauses.json")
    case = read(PREVIOUS / "data/probes/0120324-total22-positive.json")
    proposal = read(PREVIOUS / "data/next-encoding-task.json")
    for name, expected in meta["source_pins"].items():
        verify(ROOT / name, expected)
    for name, expected in proposal["source_pins"].items():
        verify(PREVIOUS / name, expected)
    for name, key in [("work/original.cnf", "original_sha256"), ("work/prelude.lrat", "prelude_sha256"),
                      ("work/augmented.cnf", "augmented_sha256"), ("data/direct-clauses.json", "data_sha256"),
                      ("scripts/prepare.py", "script_sha256")]:
        verify(HERE / name, meta[key])
    directions = [0, 1, 2, 0, 3, 2, 4]
    bounds = [[1, 21], [2, 21], [1, 21], [3, 21], [1, 21], [1, 21]]
    window = [0]
    for direction in directions:
        window.append(window[-1] ^ (1 << direction))
    assert case["directions"] == directions and case["window"] == window
    assert case["bounds"] == proposal["bounds"] == bounds and case["radius"] == 9 and case["cap"] == 22
    corners = []
    for index in range(1, 7):
        centre = window[index]
        excluded = (centre ^ window[index - 1]) | (centre ^ window[index + 1])
        opposite = [centre ^ (1 << a) ^ (1 << b) for a in range(9) for b in range(a + 1, 9)
                    if not (excluded & ((1 << a) | (1 << b)))]
        independent_set = {vertex for vertex in range(512)
                           if (vertex ^ centre).bit_count() == 2 and not ((vertex ^ centre) & excluded)}
        assert len(opposite) == len(set(opposite)) == 21 and set(opposite) == independent_set
        corners.append(opposite)
    assert data["corner_lists"] == corners
    multiplicities = Counter(vertex for opposite in corners for vertex in opposite)
    assert sum(multiplicities.values()) == 126 and len(multiplicities) == 100
    original_path = HERE / "work/original.cnf"
    historical_path = PREVIOUS / "work/0120324-total22-positive/full.cnf"
    assert original_path.read_bytes() == historical_path.read_bytes()
    header, original = parse_cnf(original_path)
    assert header == (7277, 106348)
    cuts = case["cycle_cuts"]
    assert len(cuts) == len({tuple(c) for c in cuts}) == 35
    for cut in cuts:
        check_induced_cycle(cut)
    nv, rebuilt, before_cuts = rebuild_formula(window, bounds, cuts, corners)
    assert nv == header[0] and rebuilt == original and before_cuts == 106313
    rebuilt_bytes = (f"p cnf {nv} {len(rebuilt)}\n" + "".join(" ".join(map(str, c)) + " 0\n" for c in rebuilt)).encode("ascii")
    assert original_path.read_bytes() == rebuilt_bytes

    expected = []
    for position, (opposite, (lower, _)) in enumerate(zip(corners, bounds, strict=True), 1):
        for omitted in combinations(range(21), lower - 1):
            clause = tuple(-(v + 1) for i, v in enumerate(opposite) if i not in omitted)
            expected.append((position, lower, list(omitted), clause))
    assert len(expected) == 235 and len({row[3] for row in expected}) == 235
    assert Counter(row[0] for row in expected) == {1: 1, 2: 21, 3: 1, 4: 210, 5: 1, 6: 1}
    assert len(data["rows"]) == 235
    checked = []
    with (HERE / "work/prelude.lrat").open("rt", encoding="ascii") as stream:
        for index, line in enumerate(stream):
            assert index < 235
            tokens = list(map(int, line.split()))
            zero = tokens.index(0, 1)
            assert tokens[-1] == 0 and 0 not in tokens[zero + 1:-1]
            identifier, clause, hints = tokens[0], tuple(tokens[1:zero]), tokens[zero + 1:-1]
            assert identifier == 106349 + index and clause == expected[index][3]
            assert hints and all(1 <= h <= 106348 and h < identifier for h in hints)
            position, lower, omitted, _ = expected[index]
            row = data["rows"][index]
            assert row == dict(id=identifier, position=position, lower=lower, omitted_indices=omitted,
                               clause=list(clause), hints=hints)
            assert all(-512 <= literal <= -1 for literal in clause)
            propagations, conflict = replay_original_only(clause, hints, original, nv)
            checked.append(dict(id=identifier, position=position, lower=lower, omitted_indices=omitted,
                                clause_size=len(clause), hints=len(hints), propagated=propagations,
                                final_conflict_input=conflict, line_sha256=hashlib.sha256(line.encode("ascii")).hexdigest()))
    assert len(checked) == 235
    total_hints = sum(row["hints"] for row in checked)
    assert total_hints == meta["total_hints"] == 132921
    assert min(row["hints"] for row in checked) == meta["minimum_hints"] == 140
    assert max(row["hints"] for row in checked) == meta["maximum_hints"] == 1006
    assert meta["original_variables"] == nv and meta["original_clauses"] == 106348 and meta["derived_clauses"] == 235
    augmented_header, augmented = parse_cnf(HERE / "work/augmented.cnf")
    assert augmented_header == (7277, 106583)
    assert augmented[:106348] == original and augmented[106348:] == [row[3] for row in expected]
    augmented_bytes = (f"p cnf {nv} 106583\n" + "".join(" ".join(map(str, c)) + " 0\n" for c in augmented)).encode("ascii")
    assert (HERE / "work/augmented.cnf").read_bytes() == augmented_bytes
    digest(Path(__file__))
    # Rehash every pinned input once more, guarding against concurrent changes.
    for name, expected_hash in list(PINS.items()):
        verify(ROOT / name, expected_hash)
    return dict(status="PASS_INDEPENDENT_ORIGINAL_ONLY_PRELUDE_REPLAY", timestamp_utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),
                original_variables=nv, original_clauses=106348, independently_rebuilt_original=True,
                original_byte_identical_to_milestone125=True, clause_count_before_35_cycle_cuts=before_cuts,
                cycle_cuts_independently_checked=35, derived_clauses=235, clause_ids=[106349, 106583],
                direct_clauses_per_position=[1, 21, 1, 210, 1, 1], lower_bounds=[1, 2, 1, 3, 1, 1],
                corner_lists=corners, corner_occurrences=126, distinct_corners=100,
                corner_multiplicity_histogram=dict(sorted(Counter(multiplicities.values()).items())),
                selected_vertex_variable="v+1", direct_literal_polarity="negative: corner is absent",
                total_hints=total_hints, total_unit_propagations=sum(r["propagated"] for r in checked),
                final_conflicts=len(checked), minimum_hints=140, maximum_hints=1006,
                hints_reference_only_original_inputs=True, earlier_derived_hints=0, future_or_self_hints=0,
                all_hints_checked_in_order=True, augmented_is_exact_append=True, augmented_clauses=106583,
                rows=checked, source_files_sha256=PINS, seconds=time.monotonic()-start,
                scope="Independent Python reconstruction and ordered RUP replay. No solver/compiler, no complete-formula refutation, no new count floor. A later combined proof must use the original 106348 inputs and retain the 235 derivations.")


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    result = audit()
    if args.output:
        with args.output.open("x", encoding="utf-8") as stream:
            json.dump(result, stream, indent=2)
            stream.write("\n")
    print(json.dumps({k: v for k, v in result.items() if k not in ("rows", "source_files_sha256", "corner_lists")}, indent=2))


if __name__ == "__main__":
    main()
