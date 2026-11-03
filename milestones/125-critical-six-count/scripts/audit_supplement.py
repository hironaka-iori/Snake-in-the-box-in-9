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
parser.add_argument('--output',type=Path)
args=parser.parse_args()
names=['EmptyTradeoff125','ActualBounds125']
missing=[n for n in names if not (HERE/'data'/(n+'-audit.json')).exists()]
if missing:
    raise SystemExit('Pending successful receipts: '+', '.join(missing))
modules=[module_audit(n) for n in names]
byname={m['module']:m for m in modules}
assert [len(m['theorem_audits']) for m in modules]==[2,5]
for m in modules:
    verify(HERE/'scripts/check_sum.py',m['checker_sha256'])
    src=(HERE/'lean'/(m['module']+'.lean')).read_text(encoding='utf-8')
    assert not re.search(r'^\s*(?:noncomputable\s+)?def\s',src,re.M)
runs=[]
seen=set()
for path in sorted((HERE/'logs').glob('check-run-*.json')):
    run=read(path)
    if run.get('status') not in {'PASS_REQUESTED_MODULES','STOPPED'} or run.get('active') is not None:
        continue
    selected=[]
    for row in run.get('records',[]):
        n=row['module']
        if n in byname and row.get('status')=='PASS_REFERENCE_RECOVERY_MODULE' and row.get('receipt_sha256')==byname[n]['receipt_sha256']:
            selected.append(n);seen.add(n)
    if selected:
        verify(path,sha(path))
        runs.append(dict(path=display(path),sha256=sha(path),status=run['status'],matching_passed_modules=selected))
assert seen==set(names),sorted(set(names)-seen)
failed=[]
for path in sorted((HERE/'logs').glob('ActualBounds125-*-record.json')):
    r=read(path)
    if r['exit_code']==0 and not r['timeout']:
        continue
    verify(path,sha(path))
    verify(HERE/r['source_snapshot'],r['source_sha256'])
    verify(HERE/r['log'],r['log_sha256'])
    verify((HERE/r['source_snapshot']).parent/'checker.py.txt',r['checker_sha256'])
    failed.append(dict(record=display(path),sha256=sha(path),source_sha256=r['source_sha256'],
        log=display(HERE/r['log']),log_sha256=r['log_sha256'],exit_code=r['exit_code'],timeout=r['timeout'],
        scope='Preserved unsuccessful source check; not counted as a proof.'))
frozen={
    'data/proof-review.json':'30d593f55cb50b009b2d459fc3542582dbb33240ff969893d8d7f993077fdf55',
    'audit/proof-review.md':'9015cb5a39d0171acf420cbb1bfce04970dba432fe48ccffedb9e4bbcdb1b442',
    'scripts/audit_receipts.py':'5fd5267bfc545b95abddadb5b8bb8ab27a2512e7c893286b3d531f0efa315cfc'}
for rel,d in frozen.items():verify(HERE/rel,d)
pins={display(ROOT/p):sha(ROOT/p) for p in [
    'milestones/121-replacement-window-pressure/lean/ActualPair121.lean',
    'milestones/112-critical-sum-refinement/lean/ActualSum112.lean',
    'milestones/49-six-direction-pair-catalogue/lean/CycleExclusion4906.lean']}
# Small exact arithmetic and normalized-direction checks, independent of Lean.
def canon(ds):
    seen=[];out=[]
    for d in ds:
        if d not in seen:seen.append(d)
        out.append(seen.index(d))
    return out
word=[0,1,2,0,3,2,4]
assert canon(word[:6])==[0,1,2,0,3,2]
assert canon(word[1:])==[0,1,2,3,1,4]
assert 39*24+8+35*236+2*6==9216
assert 39*23+8+35*236+2*25==9215
for rel,d in verified_files.items():
    q=Path(rel);assert sha(q if q.is_absolute() else ROOT/q)==d
out=dict(status='PASS_EMPTY_TRADEOFF_AND_ACTUAL_INTERVAL_SUPPLEMENT',
    reviewed_modules=2,axiom_reports=7,modules=modules,completed_runs=runs,preserved_failed_attempts=failed,
    frozen_prior_review=frozen,
    mathematical_scope={
        'empty_tradeoffs':'Universal six-count floor24 and at least6 ordinary empty squares imply m<=234; universal floor23 and at least25 ordinary empty squares also imply m<=234. Both local floors and the large-length empty-square assumptions remain explicit.',
        'empty_scaling':'The Lean premises are anchored counts>=24 or>=100; using A=4*s0 gives ordinary counts6 or25. Charge margins at m235 are2 and1 respectively.',
        'canonical_shapes':'The seven-direction word0120324 has canonical prefix012032 and canonical suffix012314, starting at r and r+1.',
        'actual_intervals':'For an actual fitting0120324 window with the six actual internal counts totaling<=22, all six lie in[1,21], the second lies in[2,21], and the fourth in[3,21]. All bounds refer to actual counts at r+1,...,r+6.',
        'reason':'The checked prefix gives second/fourth minima2 and excludes first<=2 with fourth<=3. If fourth<=2 then fourth=2, first>=3; the checked suffix outer-sum theorem gives second+third+fifth+sixth>=19, forcing total>=24 and contradicting<=22.',
        'limit':'This proves a necessary interval restriction under total<=22. It does not exclude that restricted interval, prove total>=23, certify a native contradiction, or establish a universal six-count floor or new unconditional upper bound.'},
    verified_file_hashes=verified_files,additional_pins=pins,script_sha256=sha(Path(__file__)),
    scope='Read-only source/receipt/object/log/snapshot/checker/dependency/import audit, with manual count indexing and small arithmetic/canonicalization checks. No compiler, solver, proof replay or graph enumeration was run. The preceding Structural125 review remains byte-identical.')
if args.output:
    with args.output.open('x',encoding='utf-8',newline='\n') as f:
        json.dump(out,f,indent=2);f.write('\n')
print(json.dumps(dict(status=out['status'],reports=7,verified_unique_files=len(verified_files),additional_pins=len(pins),
    preserved_failed_attempts=len(failed),script_sha256=sha(Path(__file__)),
    output_sha256=sha(args.output) if args.output else None),indent=2))
