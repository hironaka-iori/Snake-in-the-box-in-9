"""Read-only receipt audit; no compiler, solver or proof replay.

Prints evidence by default. --output creates a new evidence file exclusively.
"""
from pathlib import Path
import argparse
import ast
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
parser.add_argument('--require-reference', action='store_true')
args = parser.parse_args()
run_path = HERE/'logs/check-run-1793674102295627900.json'
run = read(run_path)
assert run['status'] == 'PASS_REQUESTED_MODULES' and run['active'] is None
assert len(run['modules']) == len(run['records']) == 25
assert [x['module'] for x in run['records']] == run['modules']
modules = []
for record in run['records']:
    row = module_audit(record['module'])
    assert row['receipt_sha256'] == record['receipt_sha256']
    modules.append(row)
actual = next(r for r in modules if r['module'] == 'ActualOuter120')
assert len(actual['theorem_audits']) == 7

reference_path = HERE/'data/ReferenceCoverage120-audit.json'
reference = module_audit('ReferenceCoverage120') if reference_path.exists() else None
if args.require_reference:
    assert reference is not None, 'ReferenceCoverage120 receipt is still pending'
if reference:
    assert len(reference['theorem_audits']) == 4
    modules.append(reference)

keys = []
key_pins = {}
for path in sorted((ROOT/'milestones/85-reference-catalogue-union/lean').glob('ReferenceChunk[0-9][0-9].lean')):
    src = path.read_text(encoding='utf-8-sig')
    match = re.search(r'def keys\d+ : List Key := (\[.*?\n\])', src, re.S)
    assert match
    keys.extend(ast.literal_eval(match.group(1)))
    key_pins[display(path)] = sha(path)
assert len(keys) == 1378
reference_source = HERE/'lean/ReferenceCoverage120.lean'
src = reference_source.read_text(encoding='utf-8-sig')
match = re.search(r'theorem fifteen_reference_entries_refuted\s*:\s*AllRefutedList (\[.*?\]) := by', src, re.S)
assert match
fifteen = ast.literal_eval(match.group(1))
assert len(fifteen) == 15 and len({repr(k) for k in fifteen}) == 15
assert all(k in keys for k in fifteen)
new = [([0,1,2,0,3,1], [2,3,6,3,2]),
       ([0,1,2,0,3,1], [2,3,6,3,3]),
       ([0,1,2,0,3,1], [3,3,6,3,2])]
assert fifteen[:3] == new
assert [keys[i] for i in [126,127,138]] == new
remaining = [k for k in keys if k not in fifteen]
assert len(remaining) == 1363

# Snapshot stability is checked again after the audit, without starting any process.
for p, digest in verified_files.items():
    path = Path(p)
    assert sha(path if path.is_absolute() else ROOT/path) == digest
out = dict(status='PASS_ACTUAL_OUTER_AND_REFERENCE_RECEIPTS' if reference else 'PASS_ACTUAL_OUTER_REFERENCE_PENDING',
           completed_run=display(run_path), completed_run_sha256=sha(run_path),
           proof_modules=25, reviewed_modules=len(modules),
           axiom_reports=sum(len(r['theorem_audits']) for r in modules),
           reference_receipt_status='PASS' if reference else 'PENDING', modules=modules,
           reference_literal_check=dict(total=1378, discharged_list_length=15,
               new_indices=[126,127,138], new_keys=new, remaining=1363,
               checked_Lean_receipt=reference is not None,
               reference_source_sha256=sha(reference_source), key_source_pins=key_pins),
           verified_file_hashes=verified_files, script_sha256=sha(Path(__file__)),
           scope='Receipt/source/object/log/snapshot/direct-import/dependency hash and axiom-report audit; no compiler, solver or proof replay. Actual theorem excludes four outer counts<=3 on012031 with unrestricted middle. Reference closure is completed only if its successful receipt is present. No global upper bound follows from this receipt audit.')
text = json.dumps(out, indent=2)+'\n'
if args.output:
    with args.output.open('x', encoding='utf-8', newline='\n') as stream:
        stream.write(text)
    print(json.dumps(dict(status=out['status'], output=str(args.output), sha256=sha(args.output),
                         modules=len(modules), reports=out['axiom_reports'],
                         verified_unique_files=len(verified_files)), indent=2))
else:
    print(json.dumps(dict(status=out['status'], modules=len(modules), reports=out['axiom_reports'],
                         verified_unique_files=len(verified_files), reference=reference,
                         actual=actual), indent=2))
