"""Independent proof transport, core identity, and complete RUP replay audit."""
from pathlib import Path
import argparse
import ctypes
import datetime
import hashlib
import json
import time

HERE = Path(__file__).resolve().parents[1]
ROOT = HERE.parents[1]
OLD = ROOT / 'milestones/127-direct-cardinality'
PAIR = ROOT / 'milestones/128-coupled-pair'
PINS = {}


def sha(path):
    path = Path(path).resolve()
    h = hashlib.sha256()
    with path.open('rb') as stream:
        for chunk in iter(lambda: stream.read(1024 * 1024), b''):
            h.update(chunk)
    try:
        name = path.relative_to(ROOT).as_posix()
    except ValueError:
        name = str(path)
    value = h.hexdigest()
    if name in PINS:
        assert PINS[name] == value, ('Input changed', name)
    PINS[name] = value
    return value


def verify(path, expected):
    assert sha(path) == expected, str(path)


def read(path):
    sha(path)
    return json.loads(Path(path).read_text(encoding='utf-8-sig'))


def cnf(path):
    sha(path)
    clauses = []
    header = None
    with path.open('rt', encoding='ascii') as stream:
        for line in stream:
            fields = line.split()
            if not fields or fields[0] == 'c':
                continue
            if fields[0] == 'p':
                assert not clauses and header is None and fields[:2] == ['p', 'cnf']
                header = tuple(map(int, fields[2:]))
            else:
                assert header is not None
                row = tuple(map(int, fields))
                assert row[-1] == 0 and all(0 < abs(x) <= header[0] for x in row[:-1])
                clauses.append(row[:-1])
    assert header is not None and len(clauses) == header[1]
    return header, clauses


def cnf_bytes(variables, clauses):
    return (f'p cnf {variables} {len(clauses)}\n' + ''.join(' '.join(map(str, c)) + ' 0\n' for c in clauses)).encode('ascii')


def additions(path, deletion_counter=None):
    with path.open('rb') as stream:
        for line in stream:
            fields = line.split()
            if len(fields) > 1 and fields[1] == b'd':
                if deletion_counter is not None:
                    deletion_counter[0] += 1
                continue
            row = list(map(int, fields))
            zero = row.index(0, 1)
            assert row[-1] == 0 and all(h > 0 for h in row[zero + 1:-1])
            yield row[0], tuple(row[1:zero]), row[zero + 1:-1], line


def proof_line(identifier, clause, hints):
    return (' '.join(map(str, [identifier, *clause, 0, *hints, 0])) + '\n').encode('ascii')


def check_step(clause, hints, database):
    values = {}
    for lit in clause:
        assert 0 < abs(lit) <= 10175
        value = lit < 0
        assert abs(lit) not in values or values[abs(lit)] == value
        values[abs(lit)] = value
    assert hints
    for index, hint in enumerate(hints):
        assert hint in database, ('Unavailable reference', hint)
        unassigned = set()
        for lit in database[hint]:
            assert abs(lit) not in values or values[abs(lit)] != (lit > 0), ('Satisfied reference', hint)
            if abs(lit) not in values:
                unassigned.add(lit)
        assert len(unassigned) <= 1, ('Non-unit reference', hint)
        if not unassigned:
            assert index == len(hints) - 1, 'References after conflict'
            return
        lit = unassigned.pop()
        values[abs(lit)] = lit > 0
    raise AssertionError('Missing final conflict')


def replay(path, inputs, input_ceiling):
    started = time.monotonic()
    database = dict(inputs)
    last = input_ceiling
    steps = hints_count = deletions = deleted = lines = 0
    maximum_live = len(database)
    maximum_hints = 0
    active = {abs(x) for c in database.values() for x in c}
    maximum_clause = max(map(len, database.values()), default=0)
    used_inputs = set()
    last_clause = None
    consumed = hashlib.sha256()
    with path.open('rb') as stream:
        for line in stream:
            consumed.update(line)
            lines += 1
            fields = line.split()
            if len(fields) > 1 and fields[1] == b'd':
                assert fields[-1] == b'0'
                for item in fields[2:-1]:
                    identifier = int(item)
                    assert identifier in database
                    del database[identifier]
                    deleted += 1
                deletions += 1
                continue
            row = list(map(int, fields))
            zero = row.index(0, 1)
            identifier, clause, hints = row[0], tuple(row[1:zero]), row[zero + 1:-1]
            assert row[-1] == 0 and identifier > last and all(0 < h < identifier for h in hints)
            check_step(clause, hints, database)
            database[identifier] = clause
            last = identifier
            last_clause = clause
            steps += 1
            hints_count += len(hints)
            used_inputs.update(h for h in hints if h <= input_ceiling)
            active.update(abs(x) for x in clause)
            maximum_clause = max(maximum_clause, len(clause))
            maximum_hints = max(maximum_hints, len(hints))
            maximum_live = max(maximum_live, len(database))
    assert steps > 0 and last_clause == ()
    return dict(status='PASS_COMPLETE_ORDERED_RUP', deductions=steps, ordered_hints=hints_count,
                deletion_records=deletions, deleted_identifiers=deleted, physical_lines=lines,
                maximum_live_clauses=maximum_live, final_live_clauses=len(database), final_identifier=last,
                final_clause_empty=True, maximum_step_hints=maximum_hints, maximum_clause_length=maximum_clause,
                active_variable_ids=sorted(active), active_variables=len(active), maximum_variable=max(active),
                used_input_ids=sorted(used_inputs), consumed_sha256=consumed.hexdigest(), seconds=time.monotonic()-started)


def check_subsequence(source, trimmed):
    source_rows = additions(source)
    current = next(source_rows, None)
    matched = hints = 0
    for target in additions(trimmed):
        while current is not None and current[0] < target[0]:
            current = next(source_rows, None)
        assert current is not None and current == target, ('Trimmed row changed or absent', target[0])
        matched += 1
        hints += len(target[2])
        current = next(source_rows, None)
    return dict(identical_subsequence_rows=matched, ordered_hints=hints)


def memory_gate():
    class Memory(ctypes.Structure):
        _fields_ = [('length', ctypes.c_ulong), ('load', ctypes.c_ulong)] + [
            (name, ctypes.c_ulonglong) for name in ('total_physical', 'available_physical', 'total_page',
             'available_page', 'total_virtual', 'available_virtual', 'available_extended')]
    memory = Memory()
    memory.length = ctypes.sizeof(memory)
    assert ctypes.windll.kernel32.GlobalMemoryStatusEx(ctypes.byref(memory))
    assert memory.available_physical >= 1024**3
    return memory.available_physical


def audit():
    started = time.monotonic()
    available = memory_gate()
    meta = read(HERE / 'data/trimmed-certificate.json')
    core_record = read(HERE / 'data/core-search.json')
    assert core_record['status'] == 'CORE_PROOF_TRIMMED_REPLAY_PENDING' and core_record['exit_code'] == 20
    prior_review = read(HERE / 'data/branch-review.json')
    assert prior_review['native']['full_replay']['complete_refutation_checked']
    verify(HERE / 'audit/audit_branch.py', prior_review['source_files_sha256'][
        'milestones/129-fourth-count-three/audit/audit_branch.py'])
    for name, expected in meta['source_pins'].items():
        verify(ROOT / name, expected)
    verify(HERE / 'scripts/trim_certificate.py', meta['script_sha256'])
    verify(ROOT / 'milestones/109-relaxed-graph-test/upstream/milestones/10-window-aggregate/scripts/gen_lean_core.py', meta['trimming_generator_sha256'])
    verify(HERE / 'scripts/shrink_core.py', core_record['script_sha256'])
    verify(HERE / 'data/trimmed-certificate.json', core_record['prior_certificate_sha256'])
    verify(Path(core_record['command'][0]), core_record['solver_sha256'])
    for name, key in [('work/expanded.cnf', 'cnf_sha256'), ('work/expanded.raw.lrat', 'mapped_sha256'),
                      ('work/expanded.trim.lrat', 'trim_sha256'), ('work/core.cnf', 'core_sha256')]:
        verify(HERE / name, meta[key])
    for name, key in [('work/core.cnf', 'cnf_sha256'), ('work/core-unsat.raw.lrat', 'raw_sha256'),
                      ('work/core-unsat.trim.lrat', 'trimmed_sha256'), ('work/core-unsat.mapped.lrat', 'mapped_sha256'),
                      ('work/selected-core.cnf', 'selected_core_sha256'), ('logs/core-search.stdout.txt', 'stdout_sha256'),
                      ('logs/core-search.stderr.txt', 'stderr_sha256')]:
        verify(HERE / name, core_record[key])
    assert (HERE / 'work/core-unsat.raw.lrat').stat().st_size == core_record['raw_bytes']
    assert 's UNSATISFIABLE' in (HERE / 'logs/core-search.stdout.txt').read_text()
    _, original = cnf(OLD / 'work/original.cnf')
    _, native = cnf(HERE / 'work/three.cnf')
    expanded_header, expanded = cnf(HERE / 'work/expanded.cnf')
    pair = read(PAIR / 'data/pair-counter.json')['clauses']
    families = read(HERE / 'data/branch-counters.json')['families']
    branches = [c for family in families for c in family['clauses']]
    expected_expanded = original + [tuple(c) for c in pair + branches]
    assert len(original) == 106348 and len(pair) == 2863 and len(branches) == 3014
    assert expanded_header == (10175, 112225) and expanded == expected_expanded
    assert (HERE / 'work/expanded.cnf').read_bytes() == cnf_bytes(10175, expected_expanded)
    reduction = read(OLD / 'data/reduced.json')
    prelude = read(OLD / 'data/direct-clauses.json')['rows']
    removed = set(reduction['removed_clauses'])
    input_map = [i for i in range(1, 106349) if i not in removed] + list(range(106349, 106584))
    assert input_map == reduction['input_id_map'] and len(input_map) == 101666
    assert len(prelude) == 235 and [p['id'] for p in prelude] == list(range(106349, 106584))
    justified_old = original + [tuple(p['clause']) for p in prelude]
    assert native == [justified_old[i-1] for i in input_map] + [tuple(c) for c in pair + branches]
    original_database = dict(enumerate(original, 1))
    for row in prelude:
        assert all(0 < h <= 106348 for h in row['hints'])
        check_step(tuple(row['clause']), row['hints'], original_database)
    prelude_hints = sum(len(p['hints']) for p in prelude)
    assert prelude_hints == 132921

    def transport(identifier):
        if identifier <= 101666:
            old = input_map[identifier - 1]
            return old if old <= 106348 else 112225 + old - 106348
        if identifier <= 107543:
            return 106348 + identifier - 101666
        return identifier + 4917

    omitted = [0]
    mapped_steps = mapped_hints = 0
    with (HERE / 'work/expanded.raw.lrat').open('rb') as mapped:
        for row in prelude:
            assert mapped.readline() == proof_line(112225 + row['id'] - 106348, row['clause'], row['hints'])
        for identifier, clause, hints, _ in additions(HERE / 'work/three.raw.lrat', omitted):
            assert mapped.readline() == proof_line(transport(identifier), clause, [transport(h) for h in hints])
            mapped_steps += 1
            mapped_hints += len(hints)
        assert not mapped.read(1)
    assert mapped_steps == meta['native_deductions'] == 90825
    assert mapped_hints == meta['native_hints'] == 5779098
    assert omitted[0] == meta['omitted_deletion_records'] == 17870
    initial_ids = meta['core_ids']
    assert initial_ids == sorted(set(initial_ids)) and all(1 <= i <= 112225 for i in initial_ids)
    core_header, core_clauses = cnf(HERE / 'work/core.cnf')
    assert core_header == (10175, 6131) and len(initial_ids) == 6131
    assert core_clauses == [expanded[i-1] for i in initial_ids]
    assert (HERE / 'work/core.cnf').read_bytes() == cnf_bytes(10175, core_clauses)
    first_subsequence = check_subsequence(HERE / 'work/expanded.raw.lrat', HERE / 'work/expanded.trim.lrat')
    first_replay = replay(HERE / 'work/expanded.trim.lrat', {i: expanded[i-1] for i in initial_ids}, 112225)
    assert first_replay['used_input_ids'] == initial_ids
    assert first_replay['deductions'] == meta['lemmas'] == first_subsequence['identical_subsequence_rows']
    assert first_replay['ordered_hints'] == meta['hints']
    assert first_replay['active_variable_ids'] == meta['active_variable_ids']
    assert first_replay['maximum_clause_length'] == meta['max_clause_length']
    assert first_replay['maximum_step_hints'] == meta['max_step_hints']

    raw_core = replay(HERE / 'work/core-unsat.raw.lrat', dict(enumerate(core_clauses, 1)), 6131)
    assert raw_core['consumed_sha256'] == core_record['raw_sha256']
    core_subsequence = check_subsequence(HERE / 'work/core-unsat.raw.lrat', HERE / 'work/core-unsat.trim.lrat')

    def core_transport(identifier):
        return initial_ids[identifier - 1] if identifier <= 6131 else 112225 + identifier - 6131

    local_used = set()
    with (HERE / 'work/core-unsat.mapped.lrat').open('rb') as mapped:
        for identifier, clause, hints, _ in additions(HERE / 'work/core-unsat.trim.lrat'):
            assert mapped.readline() == proof_line(core_transport(identifier), clause, [core_transport(h) for h in hints])
            local_used.update(h for h in hints if h <= 6131)
        assert not mapped.read(1)
    selected_ids = [initial_ids[i - 1] for i in sorted(local_used)]
    assert selected_ids == core_record['core_ids'] and len(selected_ids) == 3652
    selected_header, selected_clauses = cnf(HERE / 'work/selected-core.cnf')
    assert selected_header == (10175, 3652) and selected_clauses == [expanded[i-1] for i in selected_ids]
    assert (HERE / 'work/selected-core.cnf').read_bytes() == cnf_bytes(10175, selected_clauses)
    selected_replay = replay(HERE / 'work/core-unsat.mapped.lrat', {i: expanded[i-1] for i in selected_ids}, 112225)
    assert selected_replay['used_input_ids'] == selected_ids
    assert selected_replay['deductions'] == core_record['lemmas'] == core_subsequence['identical_subsequence_rows']
    assert selected_replay['ordered_hints'] == core_record['hints']
    assert selected_replay['active_variable_ids'] == core_record['active_variable_ids']
    assert selected_replay['maximum_clause_length'] == core_record['max_clause_length']
    assert selected_replay['maximum_step_hints'] == core_record['max_step_hints']
    second_record = read(HERE / 'data/core2-search.json')
    assert second_record['status'] == 'CORE_PROOF_TRIMMED_REPLAY_PENDING' and second_record['exit_code'] == 20
    verify(HERE / 'scripts/refine_core.py', second_record['script_sha256'])
    verify(HERE / 'data/core-search.json', second_record['prior_certificate_sha256'])
    verify(Path(second_record['command'][0]), second_record['solver_sha256'])
    for name, key in [('work/selected-core.cnf', 'cnf_sha256'), ('work/core2-unsat.raw.lrat', 'raw_sha256'),
                      ('work/core2-unsat.trim.lrat', 'trimmed_sha256'), ('work/core2-unsat.mapped.lrat', 'mapped_sha256'),
                      ('work/selected-core2.cnf', 'selected_core_sha256'), ('logs/core2-search.stdout.txt', 'stdout_sha256'),
                      ('logs/core2-search.stderr.txt', 'stderr_sha256')]:
        verify(HERE / name, second_record[key])
    assert (HERE / 'work/core2-unsat.raw.lrat').stat().st_size == second_record['raw_bytes']
    assert 's UNSATISFIABLE' in (HERE / 'logs/core2-search.stdout.txt').read_text()
    second_raw = replay(HERE / 'work/core2-unsat.raw.lrat', dict(enumerate(selected_clauses, 1)), 3652)
    assert second_raw['consumed_sha256'] == second_record['raw_sha256']
    second_subsequence = check_subsequence(HERE / 'work/core2-unsat.raw.lrat', HERE / 'work/core2-unsat.trim.lrat')

    def second_transport(identifier):
        return selected_ids[identifier - 1] if identifier <= 3652 else 112225 + identifier - 3652

    second_local_used = set()
    with (HERE / 'work/core2-unsat.mapped.lrat').open('rb') as mapped:
        for identifier, clause, hints, _ in additions(HERE / 'work/core2-unsat.trim.lrat'):
            assert mapped.readline() == proof_line(second_transport(identifier), clause, [second_transport(h) for h in hints])
            second_local_used.update(h for h in hints if h <= 3652)
        assert not mapped.read(1)
    second_ids = [selected_ids[i - 1] for i in sorted(second_local_used)]
    assert second_ids == second_record['core_ids'] and len(second_ids) == 3500
    second_header, second_clauses = cnf(HERE / 'work/selected-core2.cnf')
    assert second_header == (10175, 3500) and second_clauses == [expanded[i-1] for i in second_ids]
    assert (HERE / 'work/selected-core2.cnf').read_bytes() == cnf_bytes(10175, second_clauses)
    second_replay = replay(HERE / 'work/core2-unsat.mapped.lrat', {i: expanded[i-1] for i in second_ids}, 112225)
    assert second_replay['used_input_ids'] == second_ids
    assert second_replay['deductions'] == second_record['lemmas'] == second_subsequence['identical_subsequence_rows']
    assert second_replay['ordered_hints'] == second_record['hints']
    assert second_replay['active_variable_ids'] == second_record['active_variable_ids']
    assert second_replay['maximum_clause_length'] == second_record['max_clause_length']
    assert second_replay['maximum_step_hints'] == second_record['max_step_hints']
    # Inspect only existing checker sources; no export or compilation is attempted.
    checker_notes = []
    for name in ['work/final_lean/LratFastO3k15.lean', 'work/final_lean/LratFastO4k15.lean']:
        path = ROOT / name
        sha(path)
        text = path.read_text(encoding='utf-8')
        assert 'litsL 255' in text and 'Nat.shiftRight x 15' in text
        checker_notes.append(dict(path=name, literal_parser_fuel=255, word_bits=15,
                                  scope='Inspected existing source only; no claim that a new export selects this checker.'))
    sha(Path(__file__))
    for name, expected in list(PINS.items()):
        verify(ROOT / name, expected)
    return dict(status='PASS_TRANSPORT_AND_COMPLETE_CORE_REFUTATIONS', timestamp_utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),
                initial_available_memory_bytes=available, trusted_inputs=112225, old_inputs=106348,
                pair_inputs=2863, branch_inputs=3014, derived_prelude_clauses=235, prelude_hints=prelude_hints,
                prelude_original_inputs_only=True, expanded_input_bytes_exact=True,
                transported_native_deductions=mapped_steps, transported_native_hints=mapped_hints,
                omitted_native_deletion_records=omitted[0], native_transport_byte_exact=True,
                initial_core_exact=True, first_trim=first_replay, raw_core=raw_core,
                local_core_trim_exact_subsequence=core_subsequence, local_to_tagged_mapping_byte_exact=True,
                selected_core_exact=True, selected_core_global_ids=selected_ids, selected_proof=selected_replay,
                selected_input_family_counts=dict(old=sum(i <= 106348 for i in selected_ids),
                    pair=sum(106348 < i <= 109211 for i in selected_ids), branch=sum(i > 109211 for i in selected_ids)),
                core2_raw=second_raw, core2_selected_proof=second_replay,
                core2_trim_exact_subsequence=second_subsequence, core2_mapping_and_selected_bytes_exact=True,
                core2_selected_global_ids=second_ids, lowest_hint_verified_candidate='core2',
                core2_selected_input_family_counts=dict(old=sum(i <= 106348 for i in second_ids),
                    pair=sum(106348 < i <= 109211 for i in second_ids), branch=sum(i > 109211 for i in second_ids)),
                inspected_checker_sources=checker_notes, source_files_sha256=PINS, seconds=time.monotonic()-started,
                scope='Complete Python RUP checks of expanded and selected cores. Pair and branch counters remain explicit trusted inputs requiring actual-snake interpretation. No claim that those counters follow from old F alone, no Lean compilation, and no conclusion for the fourth-at-least-four branch.')


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    result = audit()
    if args.output:
        with args.output.open('x', encoding='utf-8') as stream:
            json.dump(result, stream, indent=2)
            stream.write('\n')
    summary = {k: v for k, v in result.items() if k not in ('source_files_sha256', 'selected_core_global_ids', 'core2_selected_global_ids')}
    for key in ('first_trim', 'raw_core', 'selected_proof', 'core2_raw', 'core2_selected_proof'):
        summary[key] = {k: v for k, v in summary[key].items() if k not in ('active_variable_ids', 'used_input_ids')}
    print(json.dumps(summary, indent=2))


if __name__ == '__main__':
    main()
