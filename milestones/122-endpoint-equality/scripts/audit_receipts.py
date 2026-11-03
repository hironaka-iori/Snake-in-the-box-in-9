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
plan = read(HERE/'data/end26-plan.json')
extra = ['EndpointClause122', 'LratFastEndpoint122', 'EndpointGeometry122',
         'EndpointFrequency122', 'EndpointAssembly122', 'LocalEndpoint26122',
         'ActualEndpoint26122', 'EndpointBudget122', 'EndpointFrequencyTight122']
names = plan['modules'] + extra
assert len(plan['modules']) == 58 and len(names) == len(set(names)) == 67
modules = [module_audit(n) for n in names]
byname = {r['module']: r for r in modules}
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
            matches.append(n);seen.add(n)
    if matches:
        verify(path, sha(path))
        runs.append(dict(path=display(path), sha256=sha(path), run_status=run['status'],
                         matching_passed_modules=matches))
assert seen == set(names), sorted(set(names)-seen)
assert len(byname['EndpointFrequencyTight122']['theorem_audits']) == 2
assert len(byname['ActualEndpoint26122']['theorem_audits']) == 1
assert len(byname['EndpointAssembly122']['theorem_audits']) == 2
assert len(byname['EndpointBudget122']['theorem_audits']) == 3
pins = {}
def pin(path):
    path = Path(path)
    digest = sha(path)
    pins[display(path)] = digest
    return digest
input_path = HERE/'data/certificate-input-audit.json'
ia = read(input_path)
assert ia['status'] == 'PASS_ENDPOINT_CERTIFICATE_INPUTS_AND_EXPORTS'
pin(input_path)
verify(HERE/'scripts/audit_inputs.py', ia['script_sha256'])
common = [v for v in range(512) if (v^3).bit_count()==2 and (v^6).bit_count()==2]
assert len(common) == 14
inputs = []
for row, label in zip(ia['probes'], ['26','35','44'], strict=True):
    name = 'end'+label
    pp = HERE/'data'/(name+'-plan.json');p = read(pp);pin(pp)
    probe_path = ROOT/row['probe'];verify(probe_path,row['sha256']);probe=read(probe_path)
    assert p['probe_sha256']==row['sha256'] and not p['cycle_cuts']
    assert p['common_sphere']==row['common_sphere']==probe['common_sphere']==common
    assert p['endpoint_clause_size']==row['endpoint_clause_size']==498
    assert p['variables']==row['variables']==2216
    assert p['clauses']==row['clauses']==96117
    assert p['lemmas']==row['native_lemmas'] and p['hints']==row['native_hints']
    assert p['generation']['simulated'] is True
    assert len(p['modules'])==row['modules']
    verify(HERE/'scripts/certify_endpoint.py',p['script_sha256'])
    for rel,digest in p['source_files_sha256'].items():
        verify(ROOT/rel,digest)
    for rel,digest in probe['source_files_sha256'].items():
        verify(ROOT/rel,digest)
    verify(ROOT/'milestones/121-replacement-window-pressure/scripts/probe_endpoint.py',probe['script_sha256'])
    # Hash saved certificates only; do not rerun their native replay.
    verify(HERE/'work'/name/(name+'.cnf'),p['cnf_sha256'])
    verify(HERE/'work'/name/(name+'.lrat'),p['lrat_sha256'])
    solver_path=HERE/'data'/(name+'-solver.json');solver=read(solver_path);pin(solver_path)
    assert solver['cnf_sha256']==p['cnf_sha256'] and solver['exit_code']==20
    verify(HERE/'work'/name/'raw.lrat',solver['raw_sha256'])
    for port in p['ports']:
        src,dst=HERE/port['original'],HERE/port['isolated']
        verify(src,port['source_sha256']);verify(dst,port['isolated_sha256'])
        assert dst.read_text(encoding='utf-8-sig').replace('import Recovered122G.','import ')==src.read_text(encoding='utf-8-sig')
    inputs.append(dict(case=label,plan=display(pp),plan_sha256=sha(pp),core_clauses=p['core_clauses'],
        variables=p['variables'],full_clauses=p['clauses'],deductions=p['lemmas'],hints=p['hints'],
        native_simulation_recorded=True,source_ports_checked=len(p['ports']),
        kernel_replay_complete=(label=='26'),cnf_sha256=p['cnf_sha256'],lrat_sha256=p['lrat_sha256']))
port_path=HERE/'data/checker-port.json';port=read(port_path);pin(port_path)
verify(ROOT/port['source'],port['source_sha256'])
original=(ROOT/port['source']).read_text(encoding='utf-8-sig')
current=(HERE/'lean/LratFastEndpoint122.lean').read_text(encoding='utf-8-sig')
expected=original.replace('Snake9.LratFast','Snake9.LratFastEndpoint122').replace('255','1023')
assert current.strip().split('#print axioms')[0].strip()==expected.strip()
assert original.count('255')==3
pending_path=HERE/'data/pending-plan.json';pending=read(pending_path);pin(pending_path)
assert len(pending['modules'])==len(set(pending['modules']))==381
assert not set(names).intersection(pending['modules'])
pending_receipts_present = [n for n in pending['modules']
    if (HERE/'data'/(n+'-audit.json')).exists()]
# The parent may resume this plan during the bounded review. Its receipt files
# are excluded from this frozen 67-module audit, rather than called absent.
assert not (HERE/'data/ActualEndpoint122-audit.json').exists()
reports=sum(len(r['theorem_audits']) for r in modules)
for path,digest in verified_files.items():
    q=Path(path);assert sha(q if q.is_absolute() else ROOT/q)==digest
out=dict(status='PASS_67_ENDPOINT_MODULE_RECEIPTS',reviewed_modules=len(modules),
    axiom_reports=reports,modules=modules,completed_runs=runs,certificate_inputs=inputs,
    pending_plan_modules=len(pending['modules']),pending_plan_sha256=sha(pending_path),
    pending_plan_receipts_present_not_reviewed=pending_receipts_present,
    theorem_scope={
        'actual_pair26':'Closed local and actual-snake endpoint location under fitting canonical012032 window and actual count caps2,6; no unproved local-refutation premise.',
        'all_equality_cases':'EndpointAssembly122 retains explicit local endpoint premises for26,35,44. The latter two certificates and full ActualEndpoint122 remain pending.',
        'frequency':'At most13 fitting starts when BOTH centres r+2,r+4 are at distance2 from BOTH endpoints. This is not a claim that13 is attained or optimal.',
        'charge':'Conditional arithmetic using t<=13 and explicit charge/potential premises. No graph realization, checked credit assignment, or new snake upper bound follows from this receipt audit.'},
    verified_file_hashes=verified_files,additional_pins=pins,script_sha256=sha(Path(__file__)),
    scope='Read-only audit of exact current source/object/log/snapshot/dependency/import hashes, successful-run records and printed standard axioms. Three saved input/port sets checked against recorded pins. No compiler, solver, full-graph computation, CNF reconstruction or native proof replay was run.')
if args.output:
    with args.output.open('x',encoding='utf-8',newline='\n') as stream:
        json.dump(out,stream,indent=2);stream.write('\n')
print(json.dumps(dict(status=out['status'],modules=len(modules),reports=reports,
    verified_unique_files=len(verified_files),additional_pins=len(pins),
    output_sha256=sha(args.output) if args.output else None,
    source_sha256=sha(Path(__file__))),indent=2))
