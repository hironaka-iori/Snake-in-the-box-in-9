"""Independent witness controls and positive-hint proof replay for window CNFs.

This audit is supplementary; it does not replace the geometric Lean bridge.
"""
import hashlib
import json
from itertools import combinations, product
from pathlib import Path
from window_cnf import encode


def assignment(data, selected):
    values = {}
    ends = []
    for name, var in data['variables'].items():
        if name.startswith('x'):
            values[var] = int(name[1:]) in selected
        elif name.startswith('end'):
            v = int(name[3:])
            values[var] = v in selected and sum(v ^ (1 << k) in selected for k in range(9)) == 1
            ends.append(values[var])
        elif name.startswith('prefix'):
            i, j = map(int, name[6:].split('_'))
            values[var] = sum(ends[:i+1]) >= j
        elif name.startswith('missing'):
            c, i, j = map(int, name[7:].split('_'))
            pos = data['window'].index(c)
            used = {(c ^ data['window'][pos-1]).bit_length()-1,
                    (c ^ data['window'][pos+1]).bit_length()-1}
            corners = [c ^ (1 << a) ^ (1 << b) for a, b in combinations(range(9), 2)
                       if a not in used and b not in used]
            values[var] = sum(v not in selected for v in corners[:i]) >= j
        else:
            raise AssertionError(name)
    return values


def replay(prefix):
    data = json.loads(Path(prefix+'.json').read_text(encoding='utf-8'))
    clauses = {i: c for i, c in enumerate(data['clauses'], 1)}
    count = 0
    final = None
    for line in Path(prefix+'.lrat').read_text(encoding='utf-8').splitlines():
        fields = line.split()
        if fields[1] == 'd':
            for index in map(int, fields[2:-1]):
                clauses.pop(index, None)
            continue
        fields = list(map(int, fields))
        z = fields.index(0)
        identifier, clause, hints = fields[0], fields[1:z], fields[z+1:-1]
        assigned = {abs(v): v < 0 for v in clause}
        assert len(assigned) == len(clause)
        closed = False
        for hint in hints:
            assert hint > 0
            cited = clauses[hint]
            assert not any(abs(v) in assigned and assigned[abs(v)] == (v > 0) for v in cited)
            unknown = [v for v in cited if abs(v) not in assigned]
            assert len(unknown) <= 1
            if not unknown:
                closed = True
                break
            v, = unknown
            assigned[abs(v)] = v > 0
        assert closed
        clauses[identifier] = clause
        count += 1
        final = clause
    assert final == []
    return {'proof_steps': count, 'input_clauses': len(data['clauses']),
            'sha256': {ext: hashlib.sha256(Path(prefix+ext).read_bytes()).hexdigest()
                       for ext in ['.json', '.cnf', '.lrat']}}


def main():
    controls = json.loads(Path('milestones/07-window-223/data/window_model_controls.json').read_text(encoding='utf-8'))
    bank = json.loads(Path('work/bank9.json').read_text(encoding='utf-8'))
    results = []
    for control in controls['controls']:
        row = bank[control['bank_index']]['vertex_sequence']
        base = row[control['window_start']]
        order = control['coordinate_order']
        selected = {sum((((v ^ base) >> old) & 1) << new for new, old in enumerate(order)) for v in row}
        data = {'window': [0,1,3,7,6 if control['shape']=='repeated' else 15],
                'radius': control['radius'], 'alpha_target': control['alpha'], 'cycle_cuts': []}
        for compact in [False, True]:
            cnf = encode(data, compact)
            values = assignment(cnf, selected)
            for index, clause in enumerate(cnf['clauses']):
                assert any(values[abs(v)] == (v > 0) for v in clause), (control, compact, index)
            results.append({'shape': control['shape'], 'radius': control['radius'],
                            'compact': compact, 'clauses_satisfied': len(cnf['clauses'])})
    # Check the elementary Boolean recurrence independently of the encoder.
    for a,b,c,s in product([False, True], repeat=4):
        clauses = ((not a or s), (not b or not c or s), (not s or a or b), (not s or a or c))
        assert all(clauses) == (s == (a or (b and c)))
    proofs = {shape: replay(f'milestones/07-window-223/data/window_223_{shape}_compact') for shape in ['repeated', 'distinct']}
    result = {'controls': results, 'boolean_recurrence_truth_table': 'all 16 cases passed',
              'proof_replay': proofs, 'scope': 'Python validation only; geometry-to-CNF Lean proof remains open.'}
    Path('milestones/07-window-223/data/window_encoding_audit.json').write_text(json.dumps(result, indent=2)+'\n', encoding='utf-8')
    print(json.dumps({'witness_controls': len(results), 'proofs': proofs}, indent=2))

if __name__ == '__main__':
    main()
