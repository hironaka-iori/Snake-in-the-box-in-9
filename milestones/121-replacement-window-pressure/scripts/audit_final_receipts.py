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
args = parser.parse_args()
run_names = [('check-run-1793675288541682400.json',34),
             ('check-run-1793675868667246100.json',5),
             ('check-run-1793676166926701300.json',1)]
modules, runs = [], []
for filename, count in run_names:
    path = HERE/'logs'/filename
    run = read(path)
    assert run['status'] == 'PASS_REQUESTED_MODULES' and run['active'] is None
    assert len(run['modules']) == len(run['records']) == count
    assert [x['module'] for x in run['records']] == run['modules']
    for record in run['records']:
        row = module_audit(record['module'])
        assert row['receipt_sha256'] == record['receipt_sha256']
        modules.append(row)
    runs.append(dict(path=display(path),sha256=sha(path),modules=count))
assert len(modules) == len({r['module'] for r in modules}) == 40
byname = {r['module']:r for r in modules}
assert len(byname['ActualPair121']['theorem_audits']) == 18
assert len(byname['ReferenceCoverage121']['theorem_audits']) == 4
assert len(byname['EndpointArithmetic121']['theorem_audits']) == 1
assert sum(len(r['theorem_audits']) for r in modules) == 47

keys, pins = [], {}
for path in sorted((ROOT/'milestones/85-reference-catalogue-union/lean').glob('ReferenceChunk[0-9][0-9].lean')):
    src = path.read_text(encoding='utf-8-sig')
    match = re.search(r'def keys\d+ : List Key := (\[.*?\n\])',src,re.S)
    assert match
    keys.extend(ast.literal_eval(match.group(1)))
    pins[display(path)] = sha(path)
assert len(keys) == 1378
source = HERE/'lean/ReferenceCoverage121.lean'
src = source.read_text(encoding='utf-8-sig')
match = re.search(r'theorem twenty_reference_entries_refuted\s*:\s*AllRefutedList (\[.*?\]) := by',src,re.S)
assert match
twenty = ast.literal_eval(match.group(1))
assert len(twenty) == len({repr(k) for k in twenty}) == 20
assert all(k in keys for k in twenty)
new = [([0,1,2,0,3,2],c) for c in [[2,2,6,5,2],[2,2,6,5,3],[2,3,6,3,2],[2,3,6,3,3],[2,3,6,3,4]]]
assert twenty[:5] == new and [keys[i] for i in range(196,201)] == new
oldsource = ROOT/'milestones/120-nine-transition-window/lean/ReferenceCoverage120.lean'
old = ast.literal_eval(re.search(r'theorem fifteen_reference_entries_refuted\s*:\s*AllRefutedList (\[.*?\]) := by',oldsource.read_text(encoding='utf-8-sig'),re.S).group(1))
assert twenty[5:] == old
pins[display(oldsource)] = sha(oldsource)
assert len([k for k in keys if k not in twenty]) == 1358

boundary_path = HERE/'data/boundary-paths.json'
boundary = read(boundary_path)
assert boundary['status'] == 'PASS_INDEPENDENT_FULL_Q9_BOUNDARY_PATHS'
pins[display(boundary_path)] = sha(boundary_path)
for rel,digest in boundary['source_pins'].items():
    verify(ROOT/rel,digest)
verify(HERE/'scripts/audit_boundary_paths.py',boundary['script_sha256'])
witnesses = []
for row in boundary['paths']:
    name = 'Boundary'+row['label']
    assert len(byname[name]['theorem_audits']) == 8
    source = HERE/'lean'/(name+'.lean')
    src = source.read_text(encoding='utf-8-sig')
    order = ast.literal_eval(re.search(r'private def values : Array Nat := #(\[.*?\])',src,re.S).group(1))
    assert order == row['order'] and len(order)==row['vertices'] and len(set(order))==len(order)
    assert all(0<=v<512 for v in order)
    size = int(re.search(r'def witness : Snake (\d+)',src).group(1))
    assert size == row['edges'] == len(order)-1
    w = re.search(r'theorem window_word : dsOf witness (\d+) 6 = (\[.*?\])',src)
    assert w
    start,word = int(w.group(1)),ast.literal_eval(w.group(2))
    assert start == row['start'] and word == [0,1,2,0,3,2]
    assert start+6 <= size
    assert [(order[start+j]^order[start+j+1]).bit_length()-1 for j in range(6)] == word
    c = re.search(r'theorem counts : coreAlpha witness (\d+) = (\d+) ∧\s*coreAlpha witness (\d+) = (\d+)',src)
    assert c
    i,a,j,b = map(int,c.groups())
    assert (i,j)==(start+2,start+4) and [a,b] == row['pair'] and a+b==8
    S=set(order)
    checked_counts=[]
    for pos in [i,j]:
        used={(order[pos]^order[pos-1]).bit_length()-1,(order[pos]^order[pos+1]).bit_length()-1}
        count=sum((order[pos]^(1<<x)^(1<<y)) not in S for x in range(9) for y in range(x+1,9) if x not in used and y not in used)
        checked_counts.append(count)
    assert checked_counts==[a,b]
    endpoint_distances=[[(ep^order[pos]).bit_count() for pos in [i,j]] for ep in [order[0],order[-1]]]
    assert endpoint_distances==[[2,2],[2,2]]
    witnesses.append(dict(module=name,edges=size,start=start,word=word,pair=[a,b],pair_positions=[i,j],
        source_sha256=sha(source),receipt_sha256=byname[name]['receipt_sha256'],endpoint_distances=endpoint_distances))

endpoint_audit_path=HERE/'data/endpoint-probe-audit.json'
ea=read(endpoint_audit_path)
assert ea['status']=='PASS_ENDPOINT_PROBE_ENCODING_AND_PROVENANCE_ONLY'
pins[display(endpoint_audit_path)]=sha(endpoint_audit_path)
verify(HERE/'scripts/audit_endpoint_probes.py',ea['script_sha256'])
endpoint_probes=[]
for record in ea['probes']:
    path=HERE/record['probe'];verify(path,record['sha256']);p=read(path)
    assert p['status']=='UNSAT_UNCERTIFIED' and p['radius']==9 and not p['cycle_cuts']
    assert p['counted_centres']==[3,6]
    common=[v for v in range(512) if (v^3).bit_count()==2 and (v^6).bit_count()==2]
    assert p['common_sphere']==record['common_sphere']==common and len(common)==14
    endpoint_probes.append(dict(path=display(path),sha256=sha(path),status=p['status'],cuts=0,
        scope='Encoding/provenance audit and unverified native contradiction; no refutation replay or endpoint theorem'))
assert len(endpoint_probes)==3
note=HERE/'mathematical-note.md';pins[display(note)]=sha(note)
assert 'No refutation replay or Lean proof of this endpoint' in note.read_text(encoding='utf-8')

for p,digest in verified_files.items():
    path=Path(p)
    assert sha(path if path.is_absolute() else ROOT/path)==digest
out=dict(status='PASS_PAIR_REFERENCE_BOUNDARY_AND_CONDITIONAL_ARITHMETIC_RECEIPTS',
    completed_runs=runs,proof_modules=34,reviewed_modules=40,axiom_reports=47,modules=modules,
    reference_literal_check=dict(total=1378,discharged=20,new_indices=list(range(196,201)),new_keys=new,remaining=1358),
    boundary_witnesses=witnesses,endpoint_probes=endpoint_probes,
    endpoint_scope='Only the conditional charge arithmetic is Lean checked. The endpoint-location hypothesis and frequency bound14 are unproved. Three native UNSAT probes have no refutation replay.',
    verified_file_hashes=verified_files,additional_pins=pins,script_sha256=sha(Path(__file__)),
    scope='Receipt/source/object/log/snapshot/dependency and direct-import audit with literal-reference and exact-witness checks. No compiler, solver, full-graph computation or proof replay. Generic encoded guards retain href; concrete pair minima/sum do not. No new global bound.')
if args.output:
    with args.output.open('x',encoding='utf-8',newline='\n') as stream:
        json.dump(out,stream,indent=2);stream.write('\n')
print(json.dumps(dict(status=out['status'],modules=40,reports=47,verified_unique_files=len(verified_files),
    output_sha256=sha(args.output) if args.output else None,source_sha256=sha(Path(__file__))),indent=2))
