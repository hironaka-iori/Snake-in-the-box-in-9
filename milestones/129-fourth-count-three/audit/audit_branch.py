"""Independent audit of the fourth-count-three input and terminal native evidence."""
from pathlib import Path
from collections import Counter
from itertools import combinations
import argparse
import ctypes
import datetime
import hashlib
import json
import time

HERE = Path(__file__).resolve().parents[1]
ROOT = HERE.parents[1]
PRIOR = ROOT / 'milestones/128-coupled-pair'
PINS = {}


def sha(path):
    path = Path(path).resolve()
    h = hashlib.sha256()
    with path.open('rb') as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b''):
            h.update(block)
    try:
        name = path.relative_to(ROOT).as_posix()
    except ValueError:
        name = str(path)
    result = h.hexdigest()
    if name in PINS:
        assert PINS[name] == result, ('Changed input', name)
    PINS[name] = result
    return result


def read(path):
    sha(path)
    return json.loads(Path(path).read_text(encoding='utf-8-sig'))


def verify(path, expected):
    assert sha(path) == expected, ('Hash mismatch', str(path))


def parse_cnf(path):
    sha(path)
    header = None
    clauses = []
    with path.open('rt', encoding='ascii') as stream:
        for line in stream:
            fields = line.split()
            if not fields or fields[0] == 'c':
                continue
            if fields[0] == 'p':
                assert header is None and not clauses and fields[:2] == ['p', 'cnf'] and len(fields) == 4
                header = tuple(map(int, fields[2:]))
            else:
                assert header is not None
                numbers = tuple(map(int, fields))
                assert numbers[-1] == 0 and all(0 < abs(x) <= header[0] for x in numbers[:-1])
                clauses.append(numbers[:-1])
    assert header is not None and len(clauses) == header[1]
    return header, clauses


def serialize(variables, clauses):
    return (f'p cnf {variables} {len(clauses)}\n' + ''.join(' '.join(map(str, c)) + ' 0\n' for c in clauses)).encode('ascii')


def reconstruct_counter(literals, upper, first_variable, counter_index):
    register = lambda i, j: first_variable + upper * i + j
    rows, tags = [], []
    groups = [[] for _ in literals]

    def add(clause, tag, group):
        clause = tuple(clause)
        rows.append(clause)
        tags.append(tag)
        groups[group].append(clause)

    add((-literals[0], register(0, 0)), ['first', counter_index, 0], 0)
    for j in range(1, upper):
        add((-register(0, j),), ['zero', counter_index, j], 0)
    for i in range(1, len(literals)):
        add((-literals[i], register(i, 0)), ['first', counter_index, i], i)
        add((-register(i - 1, 0), register(i, 0)), ['mono', counter_index, i - 1, 0], i)
        for j in range(1, upper):
            add((-literals[i], -register(i - 1, j - 1), register(i, j)), ['step', counter_index, i - 1, j - 1], i)
            add((-register(i - 1, j), register(i, j)), ['mono', counter_index, i - 1, j], i)
        add((-literals[i], -register(i - 1, upper - 1)), ['over', counter_index, i - 1], i)
    meanings = {str(register(i, j)): ['r', counter_index, i, j]
                for i in range(len(literals)) for j in range(upper)}
    local_cases = clause_evaluations = 0
    for i, literal in enumerate(literals):
        for before in range(min(i, upper) + 1):
            for true_occurrence in (0, 1):
                after = before + true_occurrence
                if after > upper:
                    continue
                values = {abs(literal): bool(true_occurrence) if literal > 0 else not bool(true_occurrence)}
                for j in range(upper):
                    values[register(i, j)] = after >= j + 1
                    if i:
                        values[register(i - 1, j)] = before >= j + 1
                for clause in groups[i]:
                    assert all(abs(x) in values for x in clause)
                    assert any(values[abs(x)] == (x > 0) for x in clause)
                    clause_evaluations += 1
                local_cases += 1
    return rows, tags, meanings, dict(local_threshold_cases=local_cases, clause_evaluations=clause_evaluations)


def replay_prefix(path, original, limit=None, variables=10175):
    class MemoryStatus(ctypes.Structure):
        _fields_ = [('length', ctypes.c_ulong), ('load', ctypes.c_ulong),
                    ('total_physical', ctypes.c_ulonglong), ('available_physical', ctypes.c_ulonglong),
                    ('total_page', ctypes.c_ulonglong), ('available_page', ctypes.c_ulonglong),
                    ('total_virtual', ctypes.c_ulonglong), ('available_virtual', ctypes.c_ulonglong),
                    ('available_extended', ctypes.c_ulonglong)]
    memory = MemoryStatus()
    memory.length = ctypes.sizeof(memory)
    assert ctypes.windll.kernel32.GlobalMemoryStatusEx(ctypes.byref(memory))
    assert memory.available_physical >= 1024**3, ('Insufficient available memory for replay', memory.available_physical)
    started = time.monotonic()
    database = {i: c for i, c in enumerate(original, 1)}
    last = len(original)
    deductions = total_hints = deleted = 0
    maximum_live = len(database)
    maximum_hints = deletion_records = physical_lines = 0
    empty = False
    final_clause = None
    consumed = hashlib.sha256()
    with path.open('rb') as stream:
        for line in stream:
            physical_lines += 1
            consumed.update(line)
            fields = line.split()
            if len(fields) > 1 and fields[1] == b'd':
                assert fields[-1] == b'0'
                for item in fields[2:-1]:
                    identifier = int(item)
                    assert identifier in database
                    del database[identifier]
                    deleted += 1
                deletion_records += 1
                continue
            numbers = list(map(int, fields))
            zero = numbers.index(0, 1)
            identifier, clause, hints = numbers[0], tuple(numbers[1:zero]), numbers[zero + 1:-1]
            assert numbers[-1] == 0 and identifier > last and hints
            assert all(0 < h < identifier and h in database for h in hints)
            assert all(0 < abs(x) <= variables for x in clause)
            assigned = {}
            for literal in clause:
                truth = literal < 0
                assert abs(literal) not in assigned or assigned[abs(literal)] == truth
                assigned[abs(literal)] = truth
            conflict = False
            for offset, hint in enumerate(hints):
                assert not conflict
                remaining = set()
                for literal in database[hint]:
                    assert abs(literal) not in assigned or assigned[abs(literal)] != (literal > 0)
                    if abs(literal) not in assigned:
                        remaining.add(literal)
                assert len(remaining) <= 1
                if remaining:
                    literal = remaining.pop()
                    assigned[abs(literal)] = literal > 0
                else:
                    conflict = True
                    assert offset == len(hints) - 1
            assert conflict
            database[identifier] = clause
            last = identifier
            deductions += 1
            total_hints += len(hints)
            maximum_hints = max(maximum_hints, len(hints))
            maximum_live = max(maximum_live, len(database))
            empty |= not clause
            final_clause = clause
            if limit is not None and deductions == limit:
                break
    if limit is None:
        assert deductions > 0 and final_clause == (), 'Complete replay did not end in an empty derived clause'
    else:
        assert deductions == limit
    return dict(status='PASS_COMPLETE_POSITIVE_RUP_BRANCH_REFUTATION' if limit is None else 'PASS_BOUNDED_PREFIX_ON_BRANCH_INPUT',
                deductions=deductions, ordered_hints=total_hints,
                deleted_identifiers_processed=deleted, last_identifier=last, empty_clause_in_prefix=empty,
                consumed_prefix_sha256=consumed.hexdigest(), complete_refutation_checked=limit is None,
                final_derived_clause_empty=final_clause == (), maximum_live_clauses=maximum_live,
                remaining_live_clauses=len(database), maximum_hints_in_step=maximum_hints,
                deletion_records=deletion_records, physical_lines=physical_lines,
                initial_available_memory_bytes=memory.available_physical, seconds=time.monotonic()-started,
                scope='Complete native proof of the exact 107543-clause restricted input when complete_refutation_checked is true. Actual-snake semantics and Lean replay remain separate.')


def inspect_model(stdout, clauses, variables, window, corners):
    literals = [int(token) for line in stdout.splitlines() if line.startswith('v ')
                for token in line.split()[1:] if token != '0']
    assert all(1 <= abs(x) <= variables for x in literals)
    assert len(set(map(abs, literals))) == len(literals)
    assignment = {abs(x): x > 0 for x in literals}
    occurring = {abs(x) for clause in clauses for x in clause}
    assert occurring <= assignment.keys()
    assert all(any(assignment[abs(x)] == (x > 0) for x in clause) for clause in clauses)
    selected = {v for v in range(512) if assignment[v + 1]}
    assert set(window) <= selected
    adjacency = {v: sorted(v ^ (1 << a) for a in range(9) if (v ^ (1 << a)) in selected) for v in selected}
    assert all(1 <= len(ns) <= 2 for ns in adjacency.values())
    endpoints = sorted(v for v in selected if len(adjacency[v]) == 1)
    assert len(endpoints) <= 2
    remaining = set(selected)
    components = []
    while remaining:
        todo, reached = [min(remaining)], set()
        while todo:
            v = todo.pop()
            if v not in remaining:
                continue
            reached.add(v)
            remaining.remove(v)
            todo.extend(adjacency[v])
        components.append(sorted(reached))
    cycles = [c for c in components if all(len(adjacency[v]) == 2 for v in c)]
    alpha = [sum(v not in selected for v in opposite) for opposite in corners]
    direct_alpha = [sum(all(v not in selected for v in (centre ^ (1 << a), centre ^ (1 << b),
                                      centre ^ (1 << a) ^ (1 << b)))
                        for a, b in combinations(range(9), 2)) for centre in window[1:-1]]
    assert alpha == direct_alpha and sum(alpha) <= 22
    assert alpha[0] >= 3 and alpha[1] >= 5 and alpha[3] == 3
    assert sum(alpha[i] for i in (2, 4, 5)) <= 11 and alpha[1] + alpha[3] >= 8
    path = None
    pair_checks = 0
    if not cycles:
        assert len(components) == 1 and len(endpoints) == 2
        path = [endpoints[0]]
        while len(path) < len(selected):
            candidates = [v for v in adjacency[path[-1]] if len(path) == 1 or v != path[-2]]
            assert len(candidates) == 1 and candidates[0] not in path
            path.append(candidates[0])
        assert path[-1] == endpoints[1] and set(path) == selected
        for i in range(len(path)):
            for j in range(i + 1, len(path)):
                assert ((path[i] ^ path[j]).bit_count() == 1) == (j == i + 1)
                pair_checks += 1
    return dict(status='PASS_COMPLETE_INDUCED_PATH' if path is not None else 'PASS_CNF_MODEL_WITH_CYCLE_COMPONENTS',
                assignment_count=len(assignment), checked_input_clauses=len(clauses), selected_vertices=sorted(selected),
                endpoints=endpoints, components=components, cycles=cycles, actual_six_counts=alpha,
                six_sum=sum(alpha), other_sum=sum(alpha[i] for i in (2, 4, 5)), path=path,
                path_length_edges=len(path) - 1 if path is not None else None, unordered_path_pairs_checked=pair_checks)


def inspect_terminal(clauses, variables, window, corners, sample):
    record = read(HERE / 'data/search.json')
    assert record['status'] != 'RUNNING', 'Native search still active; no changing trace inspected'
    verify(HERE / 'scripts/search.py', record['script_sha256'])
    verify(HERE / 'data/preparation.json', record['preparation_sha256'])
    verify(HERE / 'work/three.cnf', record['cnf_sha256'])
    verify(Path(record['command'][0]), record['solver_sha256'])
    raw = HERE / 'work/three.raw.lrat'
    verify(raw, record['raw_sha256'])
    assert raw.stat().st_size == record['raw_bytes']
    for path, key in [('logs/search.stdout.txt', 'stdout_sha256'), ('logs/search.stderr.txt', 'stderr_sha256')]:
        verify(HERE / path, record[key])
    stdout = (HERE / 'logs/search.stdout.txt').read_text(encoding='utf-8', errors='replace')
    result = dict(status=record['status'], wall_seconds=record['seconds'], raw_bytes=record['raw_bytes'],
                  cpu_seconds=record.get('kernel_cpu_seconds', 0) + record.get('user_cpu_seconds', 0))
    if record['status'] == 'NATIVE_SAT_MODEL_CHECK_PENDING':
        assert record['exit_code'] == 10 and 's SATISFIABLE' in stdout
        result['model'] = inspect_model(stdout, clauses, variables, window, corners)
    elif record['status'] == 'NATIVE_UNSAT_COMPLETE_REPLAY_PENDING':
        assert record['exit_code'] == 20 and 's UNSATISFIABLE' in stdout
        result['full_replay'] = replay_prefix(raw, clauses, variables=variables)
        assert result['full_replay']['consumed_prefix_sha256'] == record['raw_sha256']
    elif record['status'] == 'TIMEOUT':
        assert 's UNSATISFIABLE' not in stdout and 's SATISFIABLE' not in stdout
        if sample:
            result['prefix'] = replay_prefix(raw, clauses, sample)
    else:
        assert record['status'] == 'FAILED'
    return result


def audit(terminal, sample):
    start = time.monotonic()
    prep = read(HERE / 'data/preparation.json')
    details = read(HERE / 'data/branch-counters.json')
    for name, expected in prep['source_pins'].items():
        verify(ROOT / name, expected)
    verify(HERE / 'scripts/prepare.py', prep['script_sha256'])
    verify(HERE / 'work/three.cnf', prep['cnf_sha256'])
    verify(HERE / 'data/branch-counters.json', prep['counter_sha256'])
    directions = [0, 1, 2, 0, 3, 2, 4]
    window = [0]
    for axis in directions:
        window.append(window[-1] ^ (1 << axis))
    assert window == [0, 1, 3, 7, 6, 14, 10, 26]
    corners = []
    for i in range(1, 7):
        centre = window[i]
        excluded = (centre ^ window[i - 1]) | (centre ^ window[i + 1])
        opposite = [centre ^ (1 << a) ^ (1 << b) for a in range(9) for b in range(a + 1, 9)
                    if not (((1 << a) | (1 << b)) & excluded)]
        independent = {v for v in range(512) if (v ^ centre).bit_count() == 2 and not ((v ^ centre) & excluded)}
        assert len(opposite) == len(set(opposite)) == 21 and set(opposite) == independent
        corners.append(opposite)
    assert corners == details['corner_lists']
    base_header, base = parse_cnf(PRIOR / 'work/pair.cnf')
    assert base_header == (8705, 104529)
    assert (PRIOR / 'work/pair.cnf').read_bytes() == serialize(*[8705, base])
    # The retained 210 direct clauses express at least three absent corners at position four.
    base_set = set(base)
    fourth_lower = [tuple(-(v + 1) for i, v in enumerate(corners[3]) if i not in omitted)
                    for omitted in combinations(range(21), 2)]
    assert len(set(fourth_lower)) == 210 and all(c in base_set for c in fourth_lower)
    specifications = [
        ('first_lower_three', [v + 1 for v in corners[0]], 18, ['lo', 0], [1]),
        ('second_lower_five', [v + 1 for v in corners[1]], 16, ['lo', 1], [2]),
        ('fourth_upper_three', [-(v + 1) for v in corners[3]], 3, ['hi', 3], [4]),
        ('other_three_upper_eleven', sorted(-(v + 1) for i in (2, 4, 5) for v in corners[i]),
         11, ['proved_other_three'], [3, 5, 6])]
    assert len(details['families']) == 4
    fresh = 8706
    extra, registers, audits = [], {}, []
    for offset, (name, literals, upper, kind, positions) in enumerate(specifications):
        ci = 9 + offset
        rows, tags, meanings, semantics = reconstruct_counter(literals, upper, fresh, ci)
        occurrences = Counter(abs(x) - 1 for x in literals)
        histogram = {str(k): v for k, v in sorted(Counter(occurrences.values()).items())}
        expected = dict(name=name, counter_index=ci, positions=positions, literals=literals, upper=upper,
                        kind=kind, clauses=[list(c) for c in rows], tags=tags, first_new_variable=fresh,
                        last_new_variable=fresh + len(literals) * upper - 1, occurrences=len(literals),
                        distinct_vertices=len(occurrences), multiplicity_histogram=histogram)
        assert details['families'][offset] == expected
        assert prep['counters'][offset] == {k: v for k, v in expected.items() if k not in ('clauses', 'tags', 'literals')}
        audits.append({k: v for k, v in expected.items() if k not in ('clauses', 'tags')})
        audits[-1].update(clauses=len(rows), auxiliary_variables=len(meanings), semantic_check=semantics,
                         literal_polarity='positive selected' if literals[0] > 0 else 'negative absent',
                         repeated_vertices={str(v): n for v, n in occurrences.items() if n > 1},
                         clause_family_counts=dict(sorted(Counter(t[0] for t in tags).items())))
        assert not (set(registers) & set(meanings))
        registers.update(meanings)
        extra.extend(rows)
        fresh += len(literals) * upper
    assert details['registers'] == registers and len(registers) == 1470 and fresh == 10176
    assert len(extra) == 3014 and [a['clauses'] for a in audits] == [758, 676, 143, 1437]
    assert audits[-1]['occurrences'] == 63 and audits[-1]['distinct_vertices'] == 57
    assert audits[-1]['multiplicity_histogram'] == {'1': 51, '2': 6}
    header, full = parse_cnf(HERE / 'work/three.cnf')
    assert header == (10175, 107543) and full == base + extra
    assert (HERE / 'work/three.cnf').read_bytes() == serialize(10175, base + extra)
    # Apart from its necessarily different header, the base body is an exact byte prefix.
    assert (HERE / 'work/three.cnf').read_bytes().split(b'\n', 1)[1].startswith(
        (PRIOR / 'work/pair.cnf').read_bytes().split(b'\n', 1)[1])
    base_variables = {abs(x) for c in base for x in c}
    new_variables = {abs(x) for c in extra for x in c if abs(x) > 8705}
    assert new_variables == set(range(8706, 10176)) and not (new_variables & base_variables)
    assert len(base_variables) == 6248 and len(base_variables | new_variables) == 7718
    assert all(abs(x) <= 512 or abs(x) in new_variables for c in extra for x in c)
    assert prep['branch'] == 'fourth_count_equals_three' and prep['total_cap'] == 22
    assert prep['necessary_intervals'] == [[3, 21], [5, 21], [1, 21], [3, 3], [1, 21], [1, 21]]
    assert prep['other_positions'] == [3, 5, 6] and prep['other_sum_upper'] == 11
    for key, expected in dict(base_clauses=104529, new_clauses=3014, clauses=107543, declared_variables=10175,
                              occurring_variables=7718, new_variables=1470, first_new_variable=8706).items():
        assert prep[key] == expected
    native = inspect_terminal(full, header[0], window, corners, sample) if terminal else {'status': 'NOT_INSPECTED'}
    sha(Path(__file__))
    for name, expected in list(PINS.items()):
        verify(ROOT / name, expected)
    return dict(status='PASS_INDEPENDENT_FOURTH_THREE_INPUT_AUDIT', timestamp_utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),
                base_clauses=104529, new_clauses=3014, clauses=107543, declared_variables=10175,
                occurring_variables=7718, new_variables=1470, variable_range=[8706, 10175],
                independent_producer_imports=False, all_counter_bytes_tags_registers_match=True,
                base_clauses_and_body_bytes_unchanged=True, corner_lists=corners,
                retained_fourth_lower_three_direct_clauses=210, families=audits,
                threshold_local_cases=sum(a['semantic_check']['local_threshold_cases'] for a in audits),
                threshold_clause_evaluations=sum(a['semantic_check']['clause_evaluations'] for a in audits),
                native=native, source_files_sha256=PINS, seconds=time.monotonic() - start,
                scope='Only the fourth-count-equals-three branch under total at most22. Independent input reconstruction and terminal evidence as specified; no conclusion for fourth count at least4, complete six-count floor, or global bound.')


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--output', type=Path)
    parser.add_argument('--terminal', action='store_true')
    parser.add_argument('--sample', type=int, choices=[0, 1000], default=1000)
    args = parser.parse_args()
    result = audit(args.terminal, args.sample)
    if args.output:
        with args.output.open('x', encoding='utf-8') as stream:
            json.dump(result, stream, indent=2)
            stream.write('\n')
    summary = {k: v for k, v in result.items() if k not in ('source_files_sha256', 'corner_lists', 'families')}
    summary['counter_summary'] = [{k: a[k] for k in ('name', 'clauses', 'auxiliary_variables', 'literal_polarity',
                                                   'occurrences', 'distinct_vertices', 'repeated_vertices')} for a in result['families']]
    print(json.dumps(summary, indent=2))


if __name__ == '__main__':
    main()
