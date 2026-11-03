"""Read-only receipt audit; no compiler, solver or proof replay.

Prints evidence by default. --output creates a new evidence file exclusively.
"""
from pathlib import Path
import argparse
import hashlib
import json
import re

HERE = Path(__file__).resolve().parents[1]
ROOT = HERE.parents[1]
cache = {}


def sha(path):
    path = Path(path).resolve()
    st = path.stat()
    key = (str(path), st.st_size, st.st_mtime_ns)
    if key not in cache:
        cache[key] = hashlib.sha256(path.read_bytes()).hexdigest()
    return cache[key]


def read(path):
    return json.loads(Path(path).read_text(encoding='utf-8-sig'))


def display(path):
    path = Path(path).resolve()
    try:
        return path.relative_to(ROOT).as_posix()
    except ValueError:
        return str(path)


verified_files = {}


def verify(path, digest):
    path = Path(path)
    assert sha(path) == digest, str(path)
    verified_files[display(path)] = digest


def module_audit(name):
    receipt_path = HERE/'data'/(name+'-audit.json')
    r = read(receipt_path)
    verify(receipt_path, sha(receipt_path))
    assert r['module'] == name
    assert r['status'] == 'PASS_REFERENCE_RECOVERY_MODULE'
    assert r['exit_code'] == 0 and r['timeout'] is False
    source = HERE/'lean'/(name.replace('.', '/')+'.lean')
    obj = HERE/'build-isolated'/(name.replace('.', '/')+'.olean')
    snapshot = HERE/r['source_snapshot']
    checker_snapshot = snapshot.parent/'checker.py.txt'
    log = HERE/r['log']
    for p, digest in [(source, r['source_sha256']), (snapshot, r['source_sha256']),
                      (obj, r['olean_sha256']), (log, r['log_sha256']),
                      (checker_snapshot, r['checker_sha256'])]:
        verify(p, digest)
    for p, digest in r['dependencies'].items():
        path = Path(p)
        verify(path if path.is_absolute() else ROOT/path, digest)
    src = source.read_text(encoding='utf-8-sig')
    output = log.read_text(encoding='utf-8-sig')
    assert not re.search(r'\b(sorry|admit|native_decide)\b', src)
    assert 'error:' not in output and 'sorryAx' not in output
    rows = re.findall(r"'([^']+)' depends on axioms:\s*\[([^]]*)\]", output, re.S)
    rows += [(n, '') for n in re.findall(r"'([^']+)' does not depend on any axioms", output)]
    audits = [dict(theorem=n, axioms=re.findall(r'[A-Za-z][\w.]*', ax)) for n, ax in rows]
    assert audits == r['theorem_audits']
    assert len(audits) == src.count('#print axioms')
    assert all(set(a['axioms']) <= {'propext', 'Classical.choice', 'Quot.sound'} for a in audits)
    imports = []
    for imported in re.findall(r'^import ([\w.]+)$', src, re.M):
        rel = imported.replace('.', '/')+'.olean'
        found = next((Path(p)/rel for p in r['paths'] if (Path(p)/rel).exists()), None)
        assert found is not None, (name, imported)
        local_source = HERE/'lean'/(imported.replace('.', '/')+'.lean')
        if local_source.exists():
            expected = HERE/'build-isolated'/rel
            assert found.resolve() == expected.resolve(), (name, imported, str(found))
            dep_receipt = HERE/'data'/(imported+'-audit.json')
            dep = read(dep_receipt)
            verify(dep_receipt, r['dependencies'][dep_receipt.relative_to(ROOT).as_posix()])
            verify(found, dep['olean_sha256'])
            verify(local_source, dep['source_sha256'])
        else:
            verify(found, r['dependencies'][found.relative_to(ROOT).as_posix()])
        imports.append(dict(module=imported, object=display(found), sha256=sha(found)))
    return dict(module=name, receipt=display(receipt_path), receipt_sha256=sha(receipt_path),
                source_sha256=r['source_sha256'], object_sha256=r['olean_sha256'],
                log=display(log), log_sha256=r['log_sha256'],
                source_snapshot=display(snapshot), checker_snapshot=display(checker_snapshot),
                checker_sha256=r['checker_sha256'], dependency_count=len(r['dependencies']),
                seconds=r['seconds'], theorem_audits=audits, imports=imports)


parser = argparse.ArgumentParser()
parser.add_argument('--output', type=Path)
args = parser.parse_args()
module = module_audit('Structural125')
assert len(module['theorem_audits']) == 12
verify(HERE/'scripts/check_sum.py', module['checker_sha256'])
receipt = read(HERE/'data/Structural125-audit.json')
src = (HERE/'lean/Structural125.lean').read_text(encoding='utf-8')
assert not re.search(r'^\s*(?:noncomputable\s+)?def\s', src, re.M)
runs = []
for path in sorted((HERE/'logs').glob('check-run-*.json')):
    run = read(path)
    if run.get('status') not in {'PASS_REQUESTED_MODULES','STOPPED'} or run.get('active') is not None:
        continue
    for row in run.get('records',[]):
        if (row.get('module') == 'Structural125' and row.get('status') == 'PASS_REFERENCE_RECOVERY_MODULE'
            and row.get('receipt_sha256') == module['receipt_sha256']):
            verify(path,sha(path))
            runs.append(dict(path=display(path),sha256=sha(path),status=run['status']))
assert runs
# Verify the direct actual-count wrapper against its inherited successful receipt.
prior = HERE.parent/'124-six-count-cycle-pressure'
prior_receipt = prior/'data/ActualUniform124-audit.json'
pra = read(prior_receipt)
assert pra['status'] == 'PASS_REFERENCE_RECOVERY_MODULE' and pra['exit_code'] == 0 and not pra['timeout']
verify(prior_receipt,receipt['dependencies'][display(prior_receipt)])
for q,d in [(prior/'lean/ActualUniform124.lean',pra['source_sha256']),
    (prior/'build-isolated/ActualUniform124.olean',pra['olean_sha256']),
    (prior/pra['log'],pra['log_sha256']),
    (prior/pra['source_snapshot'],pra['source_sha256']),
    ((prior/pra['source_snapshot']).parent/'checker.py.txt',pra['checker_sha256'])]:
    verify(q,d)
assert module['imports'][0]['module'] == 'ActualUniform124'
assert module['imports'][0]['sha256'] == pra['olean_sha256']
# The old module counts an empty face once at each of its four vertices.
square_obj = next(Path(p)/'SquareIncidence.olean' for p in receipt['paths']
                  if (Path(p)/'SquareIncidence.olean').exists())
square_source = square_obj.with_suffix('.lean')
working_square = ROOT/'work/spectral/SquareIncidence.lean'
assert square_source.read_bytes() == working_square.read_bytes()
pins = {display(q):sha(q) for q in [square_obj,square_source,working_square,
    HERE.parent/'123-six-count-recovery/scripts/audit_receipts.py']}
from collections import Counter
from itertools import combinations
fibres = Counter()
for a,b in combinations(range(9),2):
    for v in range(512):
        face = tuple(sorted([v,v^(1<<a),v^(1<<b),v^(1<<a)^(1<<b)]))
        assert len(set(face)) == 4
        fibres[face] += 1
assert len(fibres) == 4608 and set(fibres.values()) == {4}
assert sum(fibres.values()) == 18432
for rel,d in verified_files.items():
    q=Path(rel)
    assert sha(q if q.is_absolute() else ROOT/q) == d
out = dict(status='PASS_STRUCTURAL125_RECEIPT_AND_MATHEMATICAL_SCOPE',
    reviewed_modules=1,axiom_reports=12,module=module,completed_runs=runs,
    direct_wrapper=dict(receipt=display(prior_receipt),receipt_sha256=sha(prior_receipt),
        source_sha256=pra['source_sha256'],object_sha256=pra['olean_sha256']),
    empty_square_accounting=dict(ordinary_faces=4608,anchored_faces=18432,
        anchors_per_face=4,source=display(square_source),resolved_object=display(square_obj),
        interpretation='A=totalEmptyAnchored counts each ordinary empty square four times, hence A=4*s0. This was checked from the source and a small finite face-incidence enumeration; no additional Lean conversion theorem is claimed.'),
    mathematical_scope={
        'three_local_lemmas':'Arithmetic over six arbitrary natural variables with every local inequality/exclusion explicit. No theorem in this module instantiates these premises for an actual snake window.',
        'retained_square_budget':'For actual nontrivial snakes:4*T+140*(m+1)+2*A<=36856, equivalent mathematically to T+35*(m+1)+2*s0<=9214 when A=4*s0.',
        'actual_deficit_required':'For every actual snake with m>=235, the39-block natural deficit D satisfies58+A<=2*D, hence D>=29+2*s0. No universal six-count floor is assumed.',
        'actual_bound234':'Conditional on235<=m implying2*D<=56+A, equivalentlyD<=28+2*s0, conclude m<=234.',
        'actual_empty_upper':'Conditional on a universal six-count floor25 and m>=234, A<=52, hence ordinary s0<=13.',
        'actual_bound233':'Conditional on the universal six-count floor25 and234<=m implyingA>=56, conclude m<=233. The latter lower bound corresponds to at least14 ordinary empty squares.',
        'unresolved':'Neither a universal six-count floor23/25 nor the needed deficit upper bound or empty-square lower bound is proved here. No new unconditional snake-length upper bound follows.'},
    verified_file_hashes=verified_files,additional_pins=pins,script_sha256=sha(Path(__file__)),
    scope='Read-only checks of current source/object/log/checker/snapshot/dependency/import hashes and all12 printed standard-axiom reports. Includes manual indexing/arithmetic review and a18432-anchor finite incidence check. No Lean compilation, solver, proof replay, or full-graph computation was run; the transitive library was not rebuilt.')
if args.output:
    with args.output.open('x',encoding='utf-8',newline='\n') as f:
        json.dump(out,f,indent=2)
        f.write('\n')
print(json.dumps(dict(status=out['status'],axiom_reports=12,
    verified_unique_files=len(verified_files),additional_pins=len(pins),
    output_sha256=sha(args.output) if args.output else None,
    script_sha256=sha(Path(__file__))),indent=2))
