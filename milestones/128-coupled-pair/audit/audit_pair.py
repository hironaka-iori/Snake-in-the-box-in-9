"""Independent pair-counter input audit; imports no producer or encoding helpers."""
from pathlib import Path
from collections import Counter
import argparse
import datetime
import hashlib
import json
import time

HERE = Path(__file__).resolve().parents[1]
ROOT = HERE.parents[1]
PRIOR = ROOT / 'milestones/127-direct-cardinality'
PINS = {}


def sha(path):
    path = Path(path).resolve()
    h = hashlib.sha256()
    with path.open('rb') as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b''):
            h.update(block)
    result = h.hexdigest()
    try:
        key = path.relative_to(ROOT).as_posix()
    except ValueError:
        key = str(path)
    if key in PINS:
        assert PINS[key] == result, ('Changed input', key)
    PINS[key] = result
    return result


def read(path):
    sha(path)
    return json.loads(Path(path).read_text(encoding='utf-8-sig'))


def check_sha(path, expected):
    assert sha(path) == expected, str(path)


def cnf(path):
    sha(path)
    clauses = []
    header = None
    with path.open('rt', encoding='ascii') as stream:
        for line in stream:
            tokens = line.split()
            if not tokens or tokens[0] == 'c':
                continue
            if tokens[0] == 'p':
                assert not clauses and header is None and tokens[:2] == ['p', 'cnf'] and len(tokens) == 4
                header = tuple(map(int, tokens[2:]))
            else:
                assert header is not None
                row = tuple(map(int, tokens))
                assert row[-1] == 0 and all(0 < abs(x) <= header[0] for x in row[:-1])
                clauses.append(row[:-1])
    assert header is not None and len(clauses) == header[1]
    return header, clauses


def serialize(variables, clauses):
    return (f'p cnf {variables} {len(clauses)}\n' + ''.join(' '.join(map(str, c)) + ' 0\n' for c in clauses)).encode('ascii')


def independent_counter(literals):
    assert len(literals) == 42 and all(1 <= x <= 512 for x in literals)
    reg = lambda i, j: 7278 + 34 * i + j
    rows, tags, groups = [], [], [[] for _ in range(42)]

    def add(clause, tag, i):
        rows.append(tuple(clause))
        tags.append(tag)
        groups[i].append(tuple(clause))

    add((-literals[0], reg(0, 0)), ['first', 8, 0], 0)
    for j in range(1, 34):
        add((-reg(0, j),), ['zero', 8, j], 0)
    for i in range(1, 42):
        add((-literals[i], reg(i, 0)), ['first', 8, i], i)
        add((-reg(i - 1, 0), reg(i, 0)), ['mono', 8, i - 1, 0], i)
        for j in range(1, 34):
            add((-literals[i], -reg(i - 1, j - 1), reg(i, j)), ['step', 8, i - 1, j - 1], i)
            add((-reg(i - 1, j), reg(i, j)), ['mono', 8, i - 1, j], i)
        add((-literals[i], -reg(i - 1, 33)), ['over', 8, i - 1], i)
    registers = {str(reg(i, j)): ['r', 8, i, j] for i in range(42) for j in range(34)}
    return rows, tags, registers, groups


def verify_threshold_extension(literals, groups):
    """Check all feasible previous-prefix counts and next-bit choices per row group."""
    assignments = evaluations = 0
    for i in range(42):
        for previous in range(min(i, 34) + 1):
            for bit in (0, 1):
                current = previous + bit
                if current > 34:
                    continue
                if i == 0:
                    assert previous == 0
                values = {literals[i]: bool(bit)}
                for j in range(34):
                    values[7278 + 34 * i + j] = current >= j + 1
                    if i:
                        values[7278 + 34 * (i - 1) + j] = previous >= j + 1
                for clause in groups[i]:
                    assert all(abs(x) in values for x in clause)
                    assert any(values[abs(x)] == (x > 0) for x in clause)
                    evaluations += 1
                assignments += 1
    # Once a prefix already has 34 true occurrences, the overflow clause rejects another.
    overflows = 0
    for i in range(34, 42):
        overflow = groups[i][-1]
        assert overflow == (-literals[i], -(7278 + 34 * (i - 1) + 33))
        overflows += 1
    return dict(feasible_local_threshold_assignments=assignments, clause_evaluations=evaluations,
                possible_first_overflow_positions=overflows,
                interpretation='register(i,j) iff at least j+1 of occurrences 0..i are selected',
                scope='Exhaustive local threshold-extension check plus exact clause schemas; general converse follows by induction, explained in review. No Lean semantic theorem claimed.')


def sample_native(clauses, limit):
    record_path = HERE / 'data/search.json'
    record = read(record_path)
    assert record['status'] != 'RUNNING', 'Native run still active; do not sample or pin its changing trace'
    check_sha(HERE / 'scripts/search.py', record['script_sha256'])
    check_sha(HERE / 'data/preparation.json', record['preparation_sha256'])
    check_sha(HERE / 'work/pair.cnf', record['cnf_sha256'])
    check_sha(Path(record['command'][0]), record['solver_sha256'])
    raw = HERE / 'work/pair.raw.lrat'
    check_sha(raw, record['raw_sha256'])
    assert raw.stat().st_size == record['raw_bytes']
    for name, key in [('logs/search.stdout.txt', 'stdout_sha256'), ('logs/search.stderr.txt', 'stderr_sha256')]:
        check_sha(HERE / name, record[key])
    database = {i: clause for i, clause in enumerate(clauses, 1)}
    last = len(clauses)
    checked = total_hints = deletions = 0
    empty = False
    prefix_hash = hashlib.sha256()
    with raw.open('rb') as stream:
        for line in stream:
            prefix_hash.update(line)
            tokens = line.split()
            if len(tokens) > 1 and tokens[1] == b'd':
                assert tokens[-1] == b'0'
                for item in tokens[2:-1]:
                    identifier = int(item)
                    assert identifier in database, ('Deletion of unavailable clause', identifier)
                    del database[identifier]
                    deletions += 1
                continue
            numbers = list(map(int, tokens))
            zero = numbers.index(0, 1)
            identifier, clause, hints = numbers[0], tuple(numbers[1:zero]), numbers[zero + 1:-1]
            assert numbers[-1] == 0 and identifier > last and hints
            assert all(0 < h < identifier and h in database for h in hints), 'Unsupported or unavailable hint'
            values = {}
            for lit in clause:
                required = lit < 0
                assert abs(lit) not in values or values[abs(lit)] == required
                values[abs(lit)] = required
            conflict = False
            for offset, hint in enumerate(hints):
                assert not conflict
                unassigned = []
                for lit in database[hint]:
                    assert abs(lit) not in values or values[abs(lit)] != (lit > 0), 'Satisfied hint'
                    if abs(lit) not in values:
                        unassigned.append(lit)
                unassigned = set(unassigned)
                assert len(unassigned) <= 1, 'Non-unit hint'
                if not unassigned:
                    conflict = True
                    assert offset == len(hints) - 1
                else:
                    lit = unassigned.pop()
                    values[abs(lit)] = lit > 0
            assert conflict
            database[identifier] = clause
            last = identifier
            total_hints += len(hints)
            checked += 1
            empty |= not clause
            if checked == limit:
                break
    assert checked == limit
    return dict(status='PASS_BOUNDED_NATIVE_PREFIX_ONLY', solver_status=record['status'],
                native_seconds=record.get('seconds'), deductions=checked, ordered_hints=total_hints,
                deleted_identifiers_processed=deletions, final_checked_identifier=last,
                empty_clause_in_checked_prefix=empty, consumed_prefix_sha256=prefix_hash.hexdigest(),
                scope='Only the first requested positive-RUP deductions were checked against the new pair input. No complete refutation or actual-snake theorem.')


def audit(sample):
    start = time.monotonic()
    prep = read(HERE / 'data/preparation.json')
    details = read(HERE / 'data/pair-counter.json')
    task = read(PRIOR / 'data/next-pair-task.json')
    for sources in (prep['source_pins'], task['source_pins']):
        for name, expected in sources.items():
            check_sha(ROOT / name, expected)
    check_sha(HERE / 'scripts/prepare.py', prep['script_sha256'])
    check_sha(HERE / 'work/pair.cnf', prep['cnf_sha256'])
    check_sha(HERE / 'data/pair-counter.json', prep['counter_sha256'])
    directions = [0, 1, 2, 0, 3, 2, 4]
    window = [0]
    for axis in directions:
        window.append(window[-1] ^ (1 << axis))
    assert window == [0, 1, 3, 7, 6, 14, 10, 26]
    two_lists = []
    for position in (2, 4):
        centre = window[position]
        used = (centre ^ window[position - 1]) | (centre ^ window[position + 1])
        ordered = [centre ^ (1 << a) ^ (1 << b) for a in range(9) for b in range(a + 1, 9)
                   if not (used & ((1 << a) | (1 << b)))]
        enumerated = {v for v in range(512) if (v ^ centre).bit_count() == 2 and not ((v ^ centre) & used)}
        assert len(ordered) == len(set(ordered)) == 21 and set(ordered) == enumerated
        two_lists.append(ordered)
    vertices = two_lists[0] + two_lists[1]
    literals = [v + 1 for v in vertices]
    assert vertices == task['pair_vertices'] == details['vertices']
    assert literals == task['selected_literal_occurrences'] == details['literals']
    counts = Counter(vertices)
    doubled = sorted(v for v, count in counts.items() if count == 2)
    assert len(vertices) == 42 and len(counts) == 37 and doubled == [18, 34, 66, 130, 258]
    assert Counter(counts.values()) == {1: 32, 2: 5}
    assert details['upper'] == task['selected_sum_upper'] == prep['pair_selected_upper'] == 34
    assert prep['pair_absent_lower'] == task['known_pair_sum_lower'] == 8 and 42 - 8 == 34
    assert prep['pair_positions'] == task['known_pair_positions'] == [2, 4]
    base_header, base = cnf(PRIOR / 'work/reduced.cnf')
    assert base_header == (7277, 101666)
    original_header, original = cnf(PRIOR / 'work/original.cnf')
    reduction = read(PRIOR / 'data/reduced.json')
    direct = read(PRIOR / 'data/direct-clauses.json')
    removed = set(reduction['removed_clauses'])
    assert len(removed) == 4917 and original_header == (7277, 106348)
    expected_base = [clause for i, clause in enumerate(original, 1) if i not in removed]
    expected_base += [tuple(row['clause']) for row in direct['rows']]
    assert len(direct['rows']) == 235 and base == expected_base
    assert (PRIOR / 'work/reduced.cnf').read_bytes() == serialize(7277, base)
    pair, tags, registers, groups = independent_counter(literals)
    assert len(pair) == 2863 and len(registers) == 1428
    assert details['clauses'] == [list(c) for c in pair] and details['tags'] == tags
    assert details['registers'] == registers and details['counter_index'] == prep['counter_index'] == 8
    header, full = cnf(HERE / 'work/pair.cnf')
    assert header == (8705, 104529) and full == base + pair
    assert (HERE / 'work/pair.cnf').read_bytes() == serialize(8705, base + pair)
    base_variables = {abs(x) for c in base for x in c}
    new_variables = {abs(x) for c in pair for x in c if abs(x) > 7277}
    assert new_variables == set(range(7278, 8706)) and not (new_variables & base_variables)
    assert len(base_variables) == 4820 and len(base_variables | new_variables) == 6248
    assert all(abs(x) <= 512 or abs(x) in new_variables for c in pair for x in c)
    expected_fields = dict(base_clauses=101666, new_counter_clauses=2863, clauses=104529,
                           declared_variables=8705, occurring_variables=6248, new_variables=1428,
                           first_new_variable=7278, pair_occurrences=42, pair_distinct_vertices=37)
    assert all(prep[k] == v for k, v in expected_fields.items())
    semantics = verify_threshold_extension(literals, groups)
    prefix = sample_native(full, sample) if sample else {'status': 'NOT_INSPECTED', 'scope': 'Input audit only'}
    sha(Path(__file__))
    for name, expected in list(PINS.items()):
        check_sha(ROOT / name, expected)
    return dict(status='PASS_INDEPENDENT_PAIR_COUNTER_INPUT_AUDIT', timestamp_utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),
                **expected_fields, first_new_variable_id=7278, last_new_variable_id=8705,
                exact_base_bytes_and_clauses=True, original_retained_plus_direct_relation_checked=True,
                exact_new_counter_serialization=True, source_producer_imports=False,
                centres=[3, 6], internal_positions=[2, 4], ordered_corner_lists=two_lists,
                occurrence_vertices=vertices, selected_literal_occurrences=literals,
                doubled_vertices=doubled, multiplicity_histogram={'1': 32, '2': 5},
                clause_family_counts=dict(sorted(Counter(t[0] for t in tags).items())),
                fresh_variables_disjoint=True, positive_selected_occurrences=True,
                counter_semantics=semantics, native_prefix=prefix, source_files_sha256=PINS,
                seconds=time.monotonic() - start,
                scope='Independent finite input audit and bounded native prefix if requested. The new pair constraint uses the proved actual-snake inequality; no RUP derivation from the old local input, complete contradiction, or completed new Lean bridge is asserted.')


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--output', type=Path)
    parser.add_argument('--sample', type=int, default=0, choices=[0, 1000])
    args = parser.parse_args()
    result = audit(args.sample)
    if args.output:
        with args.output.open('x', encoding='utf-8') as stream:
            json.dump(result, stream, indent=2)
            stream.write('\n')
    print(json.dumps({k: v for k, v in result.items() if k not in ('source_files_sha256', 'occurrence_vertices',
                       'ordered_corner_lists', 'selected_literal_occurrences')}, indent=2))


if __name__ == '__main__':
    main()
