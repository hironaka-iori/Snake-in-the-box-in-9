"""Check certificate identity, Lean replay coverage, and independent geometric controls."""
from pathlib import Path
from fractions import Fraction
import collections, gzip, hashlib, json, re, subprocess, sys

HERE = Path(__file__).resolve().parents[1]
ROOT = HERE.parents[1]
sys.path.insert(0, str(ROOT/'milestones/28-direct-share-certificates/scripts'))
sys.path.insert(0, str(ROOT/'milestones/52-share-on-235/scripts'))
from tagged_share import TaggedShare
from geometry_helpers import forest, shares

def read(name):
    return json.loads((HERE/name).read_text(encoding='utf-8'))

def sha(data):
    return hashlib.sha256(data).hexdigest()

def raw(name):
    path = HERE/'certificates'/name
    return path.read_bytes() if path.exists() else gzip.decompress(path.with_name(path.name+'.gz').read_bytes())

def cnf(name):
    return [list(map(int, line.split()))[:-1] for line in raw(name).decode().splitlines()
            if line and not line.startswith(('p', 'c'))]

certificates = []
for row, expected_hints in [(0, 1245746), (5, 716736)]:
    stem = f'obstruction{row}_95'
    module = f'ShareObstruction53{row}'
    meta = read(f'data/{stem}.json')
    enc = TaggedShare(meta['directions'], meta['bounds'], 95)
    assert enc.clauses == cnf(stem+'.full.cnf')
    assert len(enc.clauses) == meta['clauses'] == 445111 and enc.nv == meta['variables']
    ids = [i-1 for i in meta['source_original_clause_ids']]
    core = [enc.clauses[i] for i in ids]
    rename = {int(k): v for k, v in meta['original_to_new'].items()}
    compact = [[(-1 if v < 0 else 1)*rename[abs(v)] for v in clause] for clause in core]
    assert compact == cnf(stem+'.cnf')
    assert len(core) == meta['core_clauses']
    used = {abs(v) for clause in core for v in clause}
    needed = used | {abs(v) for ls, k, kind in enc.ctrs for v in ls} | {abs(v) for ls, kind in enc.tots for v in ls}
    assert set(rename) == needed and len(set(rename.values())) == len(rename)
    source = (HERE/f'lean/LocalWindowCnf/{module}.lean').read_text(encoding='utf-8')
    body = source.split('def raw : List (List Nat) := [', 1)[1].split('def cnf', 1)[0]
    leanraw = [[int(v) for v in clause.split(',') if v.strip()]
               for clause in re.findall(r'\[([0-9, ]*)\]', body)]
    assert leanraw == [[2*v if v > 0 else -2*v+1 for v in clause] for clause in compact]
    assert dict(collections.Counter(enc.tags[i][0] for i in ids)) == meta['families']
    assert meta['families']['shareCap'] == 1 and meta['families']['shareCl'] > 0
    assert 's VERIFIED' in (HERE/f'logs/{stem}-drat-check.txt').read_text()
    export = read(f'logs/{stem}-export.txt')
    assert export['simulated'] and export['hints'] == expected_hints
    assignment = read(f'data/assignment-controls{row}.json')
    assert assignment['status'] == 'PASSED' and len(assignment['rows']) == 4
    assert all(r['clauses_checked'] == 445111 for r in assignment['rows'])
    assert assignment['rows'][0]['only_expected_premise_failures'] == 1
    certificates.append(dict(row=row, directions=meta['directions'], bounds=meta['bounds'],
                             core_clauses=len(core), active_variables=len(used),
                             semantic_variables=len(needed), hints=expected_hints, checked_share=96))

for row in read('data/archives.json'):
    assert sha(raw(row['file'])) == row['sha256']
    assert sha((HERE/'certificates'/(row['file']+'.gz')).read_bytes()) == row['archive_sha256']

for row in read('data/provenance.json')['files']:
    assert sha((HERE/'data/upstream'/Path(row['path']).name).read_bytes()) == row['sha256']

# This independently recomputes every ordinary control and the count-cycle reconstruction.
subprocess.run([sys.executable, '-X', 'utf8', str(HERE/'scripts/audit_obstruction.py')], check=True)
obstruction = read('data/obstruction-audit.json')
assert obstruction['status'] == 'PASS' and len(obstruction['controls']) == 9
pair = obstruction['selected_forward_pair']
assert pair['credited_phases'] == [1, 10] and pair['share_per_period'] == 192
assert Fraction(pair['normalized_charge_mean']) == Fraction(73, 16)

# A genuine local control refutes the proposed uniform 96 bound for all nine windows.
counterexample = read('data/screen/w02.json')
assert counterexample['status'] == 'FEASIBLE'
window = [0]
for direction in counterexample['dirs']:
    window.append(window[-1] ^ (1 << direction))
selected = set(counterexample['selected'])
alpha = forest(selected, window)
share = shares(selected, window[1:-1])
assert all(lo <= a <= hi for a, (lo, hi) in zip(alpha, counterexample['alpha']))
assert sum(share) == 87 and sum(share) <= counterexample['cap']

record = read('logs/build-record.json')
build = Path((HERE/'build/latest.txt').read_text().strip())
assert str(build) == record['build']
sources = {p.relative_to(HERE/'lean').with_suffix('').as_posix(): p for p in (HERE/'lean').rglob('*.lean')}
assert len(record['records']) == len(sources)
assert {r['module'] for r in record['records']} == sources.keys()
for row in record['records']:
    assert row['exit_code'] == 0
    assert row['source_sha256'] == sha(sources[row['module']].read_bytes())
    assert (build/(row['module']+'.olean')).exists()

audits = []
for module, count in [('ObstructionPacking', 5), ('FiniteBlockBudget', 4),
                      ('LocalWindowSat-ShareObstruction530', 1), ('LocalWindowSat-ShareObstruction535', 1),
                      ('ShareBound0', 2), ('ShareBound5', 2), ('ShareInSnake0', 2), ('ShareInSnake5', 2)]:
    log = (HERE/f'logs/{module}.log').read_text(encoding='utf-8')
    assert not any(token in log for token in ['error:', 'sorryAx', 'Lean.ofReduceBool'])
    rows = re.findall(r"'([^']+)' depends on axioms:\s*\[([^]]*)\]", log, re.S)
    rows += [(name, '') for name in re.findall(r"'([^']+)' does not depend on any axioms", log)]
    assert len(rows) == count, (module, rows)
    for name, axioms in rows:
        assert {a.strip() for a in axioms.split(',') if a.strip()} <= {'propext', 'Classical.choice', 'Quot.sound'}
        audits.append(name)

out = dict(status='PASS', lean_modules=len(sources), lean_audits=len(audits),
           audited_theorems=audits, certificates=certificates, positive_controls=9,
           assignment_cases=8, assignment_clauses_per_case=445111,
           local_counterexample_share=87, count_mean='65/16',
           conditional_cyclic_charge_mean='73/16', selected_forward_phases=[1, 10],
           finite_share_bound='96*(2*p-1)',
           source_hashes={name: sha(path.read_bytes()) for name, path in sources.items()},
           scope='Two local share96 theorems for actual snakes checked in Lean. Cyclic packing and finite-block arithmetic checked under stated local and count premises. No complete run-to-snake assembly or all-cycle bound; global235 remains the contributor baseline.')
(HERE/'data/verification.json').write_text(json.dumps(out, indent=2)+'\n')
print({k: v for k, v in out.items() if k not in ['source_hashes', 'audited_theorems']})
