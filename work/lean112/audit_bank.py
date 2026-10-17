"""Audit saved kernel-build evidence without rerunning or changing the proofs."""
import hashlib
import json
import re
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
OUT = ROOT / 'outputs/lean112'
HERE = ROOT / 'work/lean112'
SEARCH = [HERE / 'bank', HERE, ROOT / 'work/lean/sat-first-checked',
          ROOT / 'work/final_lean/.lake/build/lib/lean']

def read(path):
    return json.loads(path.read_text(encoding='utf-8'))

hashes = {}
def sha(path):
    if path not in hashes:
        hashes[path] = hashlib.sha256(path.read_bytes()).hexdigest()
    return hashes[path]

def obj(name):
    return next(p / (name + '.olean') for p in SEARCH if (p / (name + '.olean')).exists())

allowed = {'propext', 'Classical.choice', 'Quot.sound'}
def audit_log(path, theorem):
    text = path.read_text(encoding='utf-8')
    lines = [s for s in text.splitlines() if f"'{theorem}' depends on axioms:" in s]
    assert len(lines) == 1, (path, theorem)
    raw = re.search(r'\[(.*)\]', lines[0])[1]
    assert set(filter(None, raw.split(', '))) <= allowed, lines[0]

state = read(OUT / 'bank-proof.json')
assert state['status'] == 'PASSED' and not state['failures'] and not state['active']
assert set(map(int, state['entries'])) == set(range(262))
assert len(state['representatives']) == 86
records = read(OUT / 'bank-module-checks.json')['modules']
for name, r in records.items():
    source = ROOT / r['source']
    assert r['exit_code'] == 0 and sha(source) == r['source_sha256'], name
    assert sha(obj(name)) == r['olean_sha256'], name
    assert not re.search(r'\b(sorry|native_decide)\b|^\s*axiom\s', source.read_text(encoding='utf-8'), re.M), name
    for dependency, expected in r['imports'].items():
        assert sha(obj(dependency)) == expected, (name, dependency)
for key, entry in state['entries'].items():
    assert entry['status'] == 'PASSED' and entry['keep_vertices'] == 112 and entry['excluded_edges'] == 192
    assert set(entry['axioms']) <= allowed
    audit_log(OUT / 'bank-logs' / (entry['module'] + '.log'), 'Snake9.Regrowth.Bank112.entry' + key)
for theorem in ['bank_no192', 'bank_no_long_prefix', 'bank_no_long_suffix', 'bank_end_segment_length_le191']:
    audit_log(OUT / 'bank-logs/Bank112Results.log', 'Snake9.Regrowth.Bank112.' + theorem)
first = read(OUT / 'first-geometric-proof.json')
assert first['status'] == 'PASSED_FIRST_GEOMETRIC_ENTRY'
for name, r in first['modules'].items():
    assert r['exit_code'] == 0 and sha(HERE / (name + '.lean')) == r['sha256'], name
    assert sha(obj(name)) == r['olean_sha256'], name
boolean = read(OUT / 'first-certificate.json')
assert boolean['status'] == 'PASSED_BOOLEAN_ONLY' and len(boolean['checked']) == 150
for r in boolean['checked']:
    source = ROOT / 'work/lean/sat-first-checked' / (r['module'] + '.lean')
    assert r['exit_code'] == 0
    assert hashlib.sha256(source.read_text(encoding='utf-8').encode()).hexdigest() == r['sha256']
    assert sha(obj(r['module'])) == r['olean_sha256']
receipt = dict(status='PASSED_SAVED_BUILD_AUDIT', entries=262, representatives=86,
    bank_build_modules=len(records), first_geometry_modules=len(first['modules']), first_boolean_modules=150,
    completed_utc=state['completed_utc'], aggregate='Bank112Results', axioms=sorted(allowed),
    evidence_sha256={n:sha(OUT / n) for n in ['bank-proof.json','bank-module-checks.json','first-geometric-proof.json','first-certificate.json']},
    scope='Conditional KEEP=112 bank end-segment exclusion; not global optimality. This audits saved kernel-build evidence, not an independent clean rebuild.')
(OUT / 'bank-final-audit.json').write_text(json.dumps(receipt, indent=2) + '\n', encoding='utf-8')
print(json.dumps(receipt, indent=2))
