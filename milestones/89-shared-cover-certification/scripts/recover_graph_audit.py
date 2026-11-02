"""Audit the completed compiler output after correcting an overly strict axiom expectation."""
from pathlib import Path
import hashlib, json, os, re

HERE = Path(__file__).resolve().parents[1]
ROOT = HERE.parents[1]
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
name = 'BalancedGraphChecks'
rp = HERE / 'data' / (name + '-audit.json')
assert not rp.exists()
record = json.loads((HERE / 'logs' / (name + '-record.json')).read_text())
assert record['exit_code'] == 0
assert sha(HERE / 'lean' / (name + '.lean')) == record['source_sha256']
log = HERE / 'logs' / (name + '.log')
assert sha(log) == record['log_sha256']
assert sha(HERE / 'data/check-balanced-covers-before-axiom-repair.py.txt') == record['checker_sha256']
for path, digest in record['dependencies'].items():
    assert sha(ROOT / path) == digest
text = log.read_text()
assert 'error:' not in text and 'sorryAx' not in text
rows = re.findall(r"'([^']+)' depends on axioms:\s*\[([^]]*)\]", text, re.S)
rows += [(n, '') for n in re.findall(r"'([^']+)' does not depend on any axioms", text)]
assert len(rows) == 3
audits = []
for theorem, axioms in rows:
    values = re.findall(r'[A-Za-z][\w.]*', axioms)
    assert set(values) <= {'propext', 'Quot.sound'}
    if theorem.endswith('graphTable_valid'):
        assert not values
    audits.append(dict(theorem=theorem, axioms=values))
fresh = HERE / 'build' / (name + '.fresh.olean')
assert fresh.is_file()
assert not (HERE / 'build' / (name + '.olean')).exists()
digest = sha(fresh)
os.replace(fresh, HERE / 'build' / (name + '.olean'))
record.update(status='PASS_BALANCED_COVER_KERNEL', olean_sha256=digest, theorem_audits=audits,
              audit_recovered_by_sha256=sha(Path(__file__)),
              recovery_reason='Compiler exited successfully. The original audit incorrectly required '
                              'the Array flattening equality to have no axioms; it uses standard '
                              'propext and Quot.sound. Source, object and compiler result are unchanged.',
              scope='Graph table validity, exact flattening identity and all-index transition equality. '
                    'No class coverage or context-witness equation is claimed.')
rp.write_text(json.dumps(record, indent=2) + '\n')
print('PASS_RECOVERED_GRAPH_AUDIT', len(audits), 'existing compiler audits; no recompile')
