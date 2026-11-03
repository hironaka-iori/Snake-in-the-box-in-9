"""Read-only receipt audit; no compiler, solver or proof replay.

Prints evidence by default. --output creates a new evidence file exclusively.
"""
from pathlib import Path
import argparse
import hashlib
import json
import re
import tarfile

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
plan_path = HERE/'data/total341-plan.json'
plan = read(plan_path)
verify(plan_path, sha(plan_path))
assert len(plan['modules']) == len(set(plan['modules'])) == 40
names = ['UniformSixBound124', 'TotalGeometry124'] + plan['modules'] + ['ActualTotal124','Reversal124','SixDeficit124','ActualUniform124']
assert len(names) == len(set(names)) == 46
missing = [n for n in names if not (HERE/'data'/(n+'-audit.json')).exists()]
if missing:
    raise SystemExit('Pending requested receipts ('+str(len(missing))+'): '+', '.join(missing))
short_checker=(HERE/'scripts/check_sum.py').read_text(encoding='utf-8')
long_checker=(HERE/'scripts/check_sum_long.py').read_text(encoding='utf-8')
assert long_checker==short_checker.replace('proc.wait(timeout=180)','proc.wait(timeout=600)')
modules = [module_audit(n) for n in names]
byname = {r['module']: r for r in modules}
for n in names:
    expected = {'UniformSixBound124':4, 'TotalGeometry124':1,
                'Recovered124G.LocalWindowSat.Total341':2, 'ActualTotal124':5,
                'Reversal124':2, 'SixDeficit124':4, 'ActualUniform124':4}.get(n,0)
    assert len(byname[n]['theorem_audits']) == expected, n
    checkers = [HERE/'scripts'/c for c in ['check_isolated.py','check_sum.py','check_sum_long.py']]
    matching = [c for c in checkers if sha(c)==byname[n]['checker_sha256']]
    assert len(matching)==1, (n, 'Unrecognized checker snapshot')
    verify(matching[0], byname[n]['checker_sha256'])
runs=[];seen=set()
for path in sorted((HERE/'logs').glob('check-run-*.json')):
    run=read(path)
    if run.get('status') not in {'PASS_REQUESTED_MODULES','STOPPED'} or run.get('active') is not None:continue
    matches=[]
    for record in run.get('records',[]):
        n=record['module']
        if n in byname and record.get('status') in {'PASS_REFERENCE_RECOVERY_MODULE','REUSED'} and record.get('receipt_sha256')==byname[n]['receipt_sha256']:
            matches.append(n);seen.add(n)
    if matches:
        verify(path,sha(path));runs.append(dict(path=display(path),sha256=sha(path),run_status=run['status'],matching_passed_modules=matches))
assert seen==set(names),sorted(set(names)-seen)
failed_attempts=[]
for path in sorted((HERE/'logs').glob('*-record.json')):
    r=read(path)
    if r.get('module') in names and (r.get('timeout') or r.get('exit_code')!=0):
        verify(path,sha(path));verify(HERE/r['log'],r['log_sha256'])
        snapshot=HERE/r['source_snapshot'];verify(snapshot,r['source_sha256'])
        verify(snapshot.parent/'checker.py.txt',r['checker_sha256'])
        failed_attempts.append(dict(record=display(path),sha256=sha(path),module=r['module'],timeout=r['timeout'],exit_code=r['exit_code'],source_sha256=r['source_sha256'],log=display(HERE/r['log']),log_sha256=r['log_sha256']))
archive_index=HERE/'data/failed-export-archives.json';archives=read(archive_index);verify(archive_index,sha(archive_index))
assert len(archives)==2
export_attempts=[]
for row in archives:
    record_path=ROOT/row['record'];record=read(record_path);verify(record_path,row['record_sha256'])
    archive=ROOT/row['archive'];verify(archive,row['archive_sha256'])
    assert record['status']=='STOPPED'
    with tarfile.open(archive,'r:gz') as tf:
        members=[m for m in tf.getmembers() if m.isfile()]
        assert len(members)==row['files']
        if record.get('plan'):
            assert record['plan']=='data/total341-plan.json' and record['plan_sha256']==sha(plan_path)
            assert record['exception']=="OSError(22, 'Invalid argument')"
            for port in plan['ports']:
                for prefix,digest in [('generated/',port['source_sha256']),('isolated/',port['isolated_sha256'])]:
                    assert hashlib.sha256(tf.extractfile(prefix+port['original']).read()).hexdigest()==digest
            for member,target in [('work/total341.cnf','work/export-total-0123041-universal-total24-full/total341.cnf'),('work/total341.lrat','work/export-total-0123041-universal-total24-full/total341.lrat'),('meta/total341.json','data/total-meta/total341.json')]:
                assert hashlib.sha256(tf.extractfile(member).read()).hexdigest()==sha(HERE/target)
    export_attempts.append(dict(record=display(record_path),record_sha256=sha(record_path),status=record['status'],exception_class=record['exception'].split('(',1)[0],complete_plan_recorded=bool(record.get('plan')),archive=display(archive),archive_sha256=sha(archive),archived_files=row['files']))
certificate_path=HERE/'data/certificate-audit.json';certificate=read(certificate_path)
verify(certificate_path,sha(certificate_path))
assert certificate['status']=='PASS_EXACT_FORMULA_MULTIPLICITIES_CORE_RUP_AND_EXPORTED_DATA'
for path,digest in certificate['source_files_sha256'].items():
    q=Path(path);verify(q if q.is_absolute() else ROOT/q,digest)
for port in plan['ports']:
    source=HERE/port['isolated'];verify(source,port['isolated_sha256'])
    n='.'.join(source.relative_to(HERE/'lean').with_suffix('').parts)
    assert n in byname and byname[n]['source_sha256']==port['isolated_sha256']
actual=(HERE/'lean/ActualTotal124.lean').read_text(encoding='utf-8')
geometry=(HERE/'lean/TotalGeometry124.lean').read_text(encoding='utf-8')
uniform=(HERE/'lean/UniformSixBound124.lean').read_text(encoding='utf-8')
reversal=(HERE/'lean/Reversal124.lean').read_text(encoding='utf-8')
deficit=(HERE/'lean/SixDeficit124.lean').read_text(encoding='utf-8')
actual_uniform=(HERE/'lean/ActualUniform124.lean').read_text(encoding='utf-8')
assert 'TotalGeometry124.actual_total_sum local_refuted p r hr hshape' in actual
assert 'Total341.sat S E ax' in actual and 'Total341.unsat tau' in actual
assert '(hr : r+7 ≤ m)' in actual and '(hshape : canon (dsOf p r 7) = [0,1,2,3,0,4,1])' in actual
assert 'actual_canonical_frame p r 7 hr' in geometry and 'frame_axioms p (mkPerm u)' in geometry
assert geometry.count('JointTags.frame_count p (mkPerm u)')==6
assert 'coreAlpha_le_21' in geometry
assert uniform.count('(hfloor : ∀ r, 0 < r → r+5 < m →')==3
assert 'total_lower_of_six_floor alpha m 38 26' in uniform and 'total_lower_of_six_floor alpha m 38 25' in uniform
assert uniform.count('35*(m+1) ≤ 9214')==2
assert 'dsOf_rev p r 7 hr' in reversal and reversal.count('coreAlpha_rev p (by omega)')==6
assert 'ActualTotal124.actual_total_sum (revSnake p) (m-r-7)' in reversal
assert 'blocks_with_deficits alpha 39 25' in deficit and '(∑ b ∈ range 39' in deficit
assert 'theorem deficit28_of_fourteen_exceptions' in deficit
refinement_path=HERE/'data/deficit-refinement.json';refinement=read(refinement_path);verify(refinement_path,sha(refinement_path))
verify(HERE/'audit/SixDeficit124-before14.lean.txt',refinement['original_sha256'])
verify(HERE/'lean/SixDeficit124.lean',refinement['source_sha256'])
assert 'GlobalCharge98.core_count_total p' in actual_uniform
assert 'SquareIncidence.global_identity p' in actual_uniform and 'SquareIncidence.wedge_total_upper p' in actual_uniform
assert actual_uniform.count('count_bounds p hm')==3
assert actual_uniform.count('(hfloor : ∀ r, 0 < r → r+5 < m →')==2
assert '(hdef : 235 ≤ m →' in actual_uniform
legacy_modules=[]
for folder,name,status in [('98-concrete-weight-integration','GlobalCharge98','PASS_CONCRETE_WEIGHT_MODULE'),('78-numeric-history-transition','CountGeometry','PASS_LEAN_MODULE')]:
    base=ROOT/'milestones'/folder;rp=base/'data'/(name+'-audit.json');r=read(rp)
    assert r['module']==name and r['status']==status and r['exit_code']==0
    assert not r.get('timeout',False)
    source=base/'lean'/(name+'.lean');obj=base/'build'/(name+'.olean');log=base/r.get('log','logs/'+name+'.log')
    for q,digest in [(rp,sha(rp)),(source,r['source_sha256']),(obj,r['olean_sha256']),(log,r['log_sha256'])]:verify(q,digest)
    text=source.read_text(encoding='utf-8');output=log.read_text(encoding='utf-8')
    assert not re.search(r'\b(sorry|admit|native_decide)\b',text)
    assert 'sorryAx' not in output and 'error:' not in output
    axrows=re.findall(r"'([^']+)' depends on axioms:\s*\[([^]]*)\]",output,re.S)
    axrows += [(n,'') for n in re.findall(r"'([^']+)' does not depend on any axioms",output)]
    audits=[dict(theorem=n,axioms=re.findall(r'[A-Za-z][\w.]*',ax)) for n,ax in axrows]
    assert audits==r['theorem_audits'] and len(audits)==text.count('#print axioms')
    assert all(set(a['axioms'])<={'propext','Classical.choice','Quot.sound'} for a in audits)
    if name=='GlobalCharge98':
        snap=base/r['source_snapshot'];verify(snap,r['source_sha256']);verify(snap.parent/'checker.py.txt',r['checker_sha256'])
        for path,digest in r['dependencies'].items():verify(ROOT/path,digest)
    else:
        summary=ROOT/'milestones/77-direction-state-coverage/data/proof-summary.json';verify(summary,r['inherited_summary_sha256'])
        support_path=base/'data/count-support.json';support=read(support_path);verify(support_path,r['count_support_sha256'])
        for row in support['modules']:
            verify(row['source'],row['source_sha256']);verify(row['object'],row['object_sha256'])
    actual_receipt=read(HERE/'data/ActualUniform124-audit.json')
    resolved=next((Path(path)/(name+'.olean') for path in actual_receipt['paths'] if (Path(path)/(name+'.olean')).exists()),None)
    assert resolved is not None and resolved.resolve()==obj.resolve()
    legacy_modules.append(dict(module=name,receipt=display(rp),receipt_sha256=sha(rp),source_sha256=r['source_sha256'],object_sha256=r['olean_sha256'],log=display(log),log_sha256=r['log_sha256'],axiom_reports=len(audits),resolved_by_actual_uniform=True))
for path,digest in verified_files.items():
    q=Path(path);assert sha(q if q.is_absolute() else ROOT/q)==digest
reports=sum(len(r['theorem_audits']) for r in modules);assert reports==22
script_path=Path(__file__);verify(script_path,sha(script_path))
out=dict(status='PASS_ALL46_MODULES_SINGLE_SHAPE_AND_CONDITIONAL_ACTUAL_BOUNDS',reviewed_modules=len(modules),axiom_reports=reports,
    modules=modules,existing_count_dependencies=legacy_modules,completed_runs=runs,preserved_export_attempts=export_attempts,preserved_failed_attempts=failed_attempts,checker_timeout_change_only=True,source_files_sha256=verified_files,script_sha256=sha(script_path),
    mathematical_review={
      'concrete_formula':'Directions0123041, vertices0,1,3,7,15,14,30,28, six bounds0..21, cap24,126occurrences/105distinct, no appended cuts.',
      'semantic_counter':'The extra sum counter is excluded from ordinary ctrOK and justified by sound_append_sum using the explicit six-centre sum premise and multiset permutation.',
      'contradiction':'The compiled core semantic theorem and compiled core LRAT contradiction are combined in ActualTotal124.local_refuted.',
      'actual_transfer':'Canonical coordinate frame and six individual frame_count equalities transfer this contradiction to coreAlpha at r+1 through r+6 under r+7<=m.',
      'single_shape_scope':'ActualTotal124 proves the forward canonical seven-transition shape0123041. Reversal124 proves the reverse orientation and combines both; no universal six-count theorem is claimed.',
      'uniform_accounting':'Disjoint six-count blocks start at6b+1, uncovered internal positions contribute at least1, and endpoints contribute at least4 each. No overlap of block charges is assumed.',
      'deficit_bound':'For39 disjoint six-count blocks, an explicit total deficit at most28 below floor25 gives conditional length at most234. If every block sum is at least23, at most13 deficient blocks give deficit at most26; the added weaker premise of at most14 deficient blocks gives deficit at most28 and still suffices for234. Those minimum and exception-count premises remain explicit.',
      'conditional_bounds':'ActualUniform124 derives endpoints, positive counts and the square budget for actual snakes. It proves m<=234 from the explicit universal six-count floor25, m<=233 from floor26, and m<=234 from the explicit39-block deficit<=28 premise. Those floor/deficit premises remain unproved.',
      'indexing':'For the geometric transfer, r+7<=m makes all six centres internal. For the generic bound,6B+1<=m reserves both endpoints and accounts for all uncovered internal counts.'},
    theorem_scope={
      'closed_single_shape':'ActualTotal124.actual_total_sum and Reversal124.actual_either prove25<=sum of six internal coreAlpha counts for a Snake m with canonical seven-direction shape0123041 in either orientation.',
      'conditional_global':'ActualUniform124 transfers the conditional bounds234/233 to actual snakes and discharges the endpoint, positivity and square-budget hypotheses. Its universal floor or block-deficit premise remains explicit. No new unconditional global snake bound is established.',
      'trusted_axioms':'Every printed axiom list is contained in propext,Classical.choice,Quot.sound. No sorryAx or native_decide was present.',
      'verification':'Read-only receipt, exact-source/object/log/snapshot/checker/dependency/import-resolution review. No solver or compiler was invoked by this auditor.'})
if args.output:
    with args.output.open('x',encoding='utf-8',newline='\n') as stream:json.dump(out,stream,indent=2);stream.write('\n')
print(json.dumps(dict(status=out['status'],modules=len(modules),axiom_reports=reports,verified_files=len(verified_files),output_sha256=sha(args.output) if args.output else None),indent=2))
