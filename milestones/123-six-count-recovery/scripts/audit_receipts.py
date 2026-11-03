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
names = ['Recovered123G.LocalWindowCnf.SixFour10',
         'Recovered123G.LocalWindowSat.SixFour10',
         'CaseSemantics123', 'SixCharge123', 'GuardedCharge123']
missing = [n for n in names if not (HERE/'data'/(n+'-audit.json')).exists()]
if missing:
    raise SystemExit('Pending requested receipts: '+', '.join(missing))
modules = [module_audit(n) for n in names]
byname = {r['module']: r for r in modules}
expected_reports = [0, 0, 1, 4, 2]
for n, count in zip(names, expected_reports, strict=True):
    assert len(byname[n]['theorem_audits']) == count
    verify(HERE/'scripts/check_isolated.py', byname[n]['checker_sha256'])
runs = []
seen = set()
for path in sorted((HERE/'logs').glob('check-run-*.json')):
    run = read(path)
    if run.get('status') not in {'PASS_REQUESTED_MODULES', 'STOPPED'} or run.get('active') is not None:
        continue
    matches = []
    for record in run.get('records', []):
        n = record['module']
        if (n in byname and record.get('status') == 'PASS_REFERENCE_RECOVERY_MODULE'
                and record.get('receipt_sha256') == byname[n]['receipt_sha256']):
            matches.append(n)
            seen.add(n)
    if matches:
        verify(path, sha(path))
        runs.append(dict(path=display(path), sha256=sha(path), run_status=run['status'],
                         matching_passed_modules=matches))
assert seen == set(names), sorted(set(names)-seen)
plan_path = HERE/'data/case10-plan.json'
plan = read(plan_path)
assert len(plan['modules']) == len(set(plan['modules'])) == 202
assert set(names[:2]) <= set(plan['modules'])
other_plan_modules = [n for n in plan['modules'] if n not in names]
other_receipts = [n for n in other_plan_modules if (HERE/'data'/(n+'-audit.json')).exists()]
pins = {display(p): sha(p) for p in [
    plan_path, HERE.parent/'122-endpoint-equality/scripts/audit_receipts.py']}
# Scope is read from the theorem statements, not the inherited receipt boilerplate.
receipt_scope = {n: read(HERE/'data'/(n+'-audit.json'))['scope'] for n in names}
for path, digest in verified_files.items():
    q = Path(path)
    assert sha(q if q.is_absolute() else ROOT/q) == digest
reports = sum(len(r['theorem_audits']) for r in modules)
assert reports == 7
out = dict(
    status='PASS_FIVE_CASE_SEMANTICS_AND_CHARGE_MODULES',
    reviewed_modules=len(modules), axiom_reports=reports,
    modules=modules, completed_runs=runs,
    mathematical_review={
        'six_window_indices':'r through r+5; r<N gives last possible index N+4, so range(N+5) is sufficient, including N=0.',
        'six_window_budget':'Nonnegative excess; each position counted at most six times; 0<=C<=20 gives total coefficient at most120.',
        'five_window_alignment':'The earlier five-centre contribution uses r+1 through r+5, the last five of the six positions. For a nine-transition graph window starting at t, use r=t+3.',
        'deficit':'The actual total lower bound remains explicit. Integer max(0,L-B) and natural truncated subtraction encode the nonnegative deficit.',
        'combination':'Alternative credits are combined by maximum. Their sum is not justified by these lemmas.',
        'guarded_coefficient24':'The first actual count must be <=6, making its excess zero; the deficit is then paid entirely by the last five excesses.',
        'symbol6_warning':'A clipped symbol6 denotes actual count6..21 and cannot alone establish the guarded premise. A first symbol<=5 is sufficient; exact actual6 needs separate evidence.',
        'source_findings':'No mathematical indexing or accounting defect found in the two reviewed arithmetic sources.'},
    theorem_scope={
        'case10_semantics':'Axioms for the fixed0123042 window and six exact counts4 imply existence of a satisfying assignment for the recovered core CNF. No core contradiction or actual-snake exclusion is proved by these five modules.',
        'six_charge':'Four generic arithmetic statements with nonnegative excess and explicit local-credit/lower-bound hypotheses.',
        'guarded_charge':'Two generic arithmetic statements; first actual count<=6 and a local sum lower bound remain hypotheses.',
        'floor26':'The universal six-count lower bound26 is not a theorem supplied by this audit. Its native UNSAT evidence is outside this receipt review.',
        'graph':'No all-edge graph certificate, actual graph weight assembly, or improved snake upper bound is established.'},
    receipt_scope_boilerplate=receipt_scope,
    metadata_caveat='The inherited receipt scope sentence mentions an actual-snake exclusion. It is inaccurate for these modules; the precise source-based scope is recorded above. Receipt bytes are preserved.',
    case10_plan_modules=len(plan['modules']),
    case10_plan_modules_outside_this_audit=len(other_plan_modules),
    outside_plan_receipts_present_not_reviewed=other_receipts,
    verified_file_hashes=verified_files, additional_pins=pins,
    script_sha256=sha(Path(__file__)),
    scope='Read-only audit of the five exact current source/object/log/snapshot/dependency/import/checker hashes, successful-run records and seven printed standard-axiom reports, plus a source-level arithmetic/indexing review. No compiler, solver, native proof replay or graph enumeration was run.')
if args.output:
    with args.output.open('x', encoding='utf-8', newline='\n') as stream:
        json.dump(out, stream, indent=2)
        stream.write('\n')
print(json.dumps(dict(status=out['status'], modules=len(modules), reports=reports,
    verified_unique_files=len(verified_files), additional_pins=len(pins),
    output_sha256=sha(args.output) if args.output else None,
    source_sha256=sha(Path(__file__))), indent=2))
