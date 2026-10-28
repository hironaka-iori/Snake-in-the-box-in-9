"""Audit completed builds, source hashes, and printed dependency lists."""
from pathlib import Path
import hashlib, json, re
HERE = Path(__file__).resolve().parents[1]
record = json.loads((HERE / 'logs/build-record.json').read_text())
sources = {p.relative_to(HERE / 'lean').with_suffix('').as_posix(): p
           for p in (HERE / 'lean').rglob('*.lean')}
assert set(sources) == {r['module'] for r in record['records']}
assert len(record['records']) == len(sources) == 80
allowed = {'propext', 'Classical.choice', 'Quot.sound'}
audits = []
for r in record['records']:
    assert r['exit_code'] == 0
    source = sources[r['module']]
    assert r['source_sha256'] == hashlib.sha256(source.read_bytes()).hexdigest()
    assert (Path(record['build']) / (r['module'] + '.olean')).is_file()
    log = (HERE / 'logs' / (r['module'].replace('/', '-') + '.log')).read_text()
    assert 'error:' not in log and 'sorryAx' not in log
    entries = re.findall(r"'([^']+)' depends on axioms: \[([^]]*)\]", log)
    entries += [(n, '') for n in re.findall(r"'([^']+)' does not depend on any axioms", log)]
    expected = 5 if r['module'].startswith('Geometry/') else {'ForcedShare': 4, 'ForcedShareBridge': 1, 'GeometryCatalogue': 0, 'WeightedCeiling': 2}[r['module']]
    assert len(entries) == expected
    for name, text in entries:
        axioms = {a.strip() for a in text.split(',') if a.strip()}
        assert axioms <= allowed
        if r['module'].startswith('Geometry/') and not name.endswith('.in_snake'):
            assert axioms <= {'propext'}
        audits.append(dict(theorem=name, axioms=sorted(axioms)))
assert len(audits) == 387
out = dict(status='PASS', modules=len(sources), audits=len(audits),
           finite_kernel_checks=304, arbitrary_snake_instances=76,
           records=record['records'], dependencies=audits,
           scope='Forced-absence share inequality and its 76 window instances in arbitrary snakes; two conditional fixed-weight arithmetic lemmas. No full finite-model-to-global-bound assembly.')
(HERE / 'data/lean-audit.json').write_text(json.dumps(out, indent=2) + '\n')
print({k:v for k,v in out.items() if k not in ['records', 'dependencies']})
