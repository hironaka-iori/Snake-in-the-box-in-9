"""Verify the completed1397-module proof without restarting any compiler."""
from pathlib import Path
import datetime,gzip,hashlib,json,re,tarfile,time
H=Path(__file__).resolve().parents[1];R=H.parents[1];S=R/'milestones/115-total-count-certificate'
read=lambda p:json.loads(p.read_text(encoding='utf-8-sig'))
cache={}
def sha(p):
    p=Path(p);key=(str(p.resolve()),p.stat().st_size,p.stat().st_mtime_ns)
    if key not in cache:
        d=hashlib.sha256()
        with p.open('rb') as f:
            for b in iter(lambda:f.read(1048576),b''):d.update(b)
        cache[key]=d.hexdigest()
    return cache[key]
start=time.monotonic();progress=S/'data/batch-progress.json';p=read(progress);progress_hash=sha(progress)
assert p['status']=='PASS_COMPLETE_TOTAL_COUNT_PROOF' and p['active'] is None
assert p['total_modules']==len(p['checked_modules'])==1397
assert not (S/'data/batch.lock').exists()
planpath=S/'data/total-plan.json';plan=read(planpath)
assert sha(planpath)==p['plan_sha256']
assert sha(S/'scripts/run_batch.py')==p['driver_sha256']
assert sha(S/'scripts/check_modules.py')==p['checker_sha256']
modules=[r['module'] for r in p['checked_modules']]
assert len(set(modules))==1397 and set(modules)==set(plan['modules'])|{'ActualTotal115'}
assert modules[-1]=='ActualTotal115'
artifacts={x['path']:x['sha256'] for x in plan['artifacts']}
files={progress,planpath,S/'scripts/run_batch.py',S/'scripts/check_modules.py'}
reports=[];rows=[];seen=set();dependency_pins={}
for k,item in enumerate(p['checked_modules'],1):
    m=item['module'];receipt=S/'data'/(m+'-audit.json');j=read(receipt)
    assert sha(receipt)==item['receipt_sha256']
    assert j['status']=='PASS_TOTAL_COUNT_MODULE' and j['exit_code']==0 and not j['timeout']
    source=S/'lean'/(m.replace('.','/')+'.lean');snapshot=S/j['source_snapshot']
    obj=S/'build'/(m.replace('.','/')+'.olean');log=S/j['log']
    assert sha(source)==sha(snapshot)==j['source_sha256']
    if m!='ActualTotal115':assert artifacts[source.relative_to(S).as_posix()]==j['source_sha256']
    assert sha(obj)==j['olean_sha256'] and sha(log)==j['log_sha256']
    checker_snapshot=snapshot.parent/'checker.py.txt'
    assert sha(checker_snapshot)==j['checker_sha256']
    source_text=source.read_text(encoding='utf-8')
    assert not re.search(r'\b(sorry|admit|native_decide|axiom)\b',source_text)
    imports=set(re.findall(r'^import ([\w.]+)$',source_text,re.M))
    assert (imports & set(modules)) <= seen,(m,imports-seen)
    seen.add(m)
    for path,digest in j['dependencies'].items():
        assert sha(path)==digest,path
        if path in dependency_pins:assert dependency_pins[path]==digest
        dependency_pins[path]=digest
    assert len(j['theorem_audits'])==item['theorem_audits']
    assert all(set(q['axioms'])<={'propext','Classical.choice','Quot.sound'} for q in j['theorem_audits'])
    reports.extend(j['theorem_audits']);files.update([receipt,snapshot,log,checker_snapshot])
    rows.append(dict(module=m,receipt_sha256=sha(receipt),source_sha256=sha(source),object_sha256=sha(obj),log_sha256=sha(log)))
    if k%250==0:print('Verified',k,'of1397',flush=True)
final=read(S/'data/ActualTotal115-audit.json')
assert len(final['theorem_audits'])==5
assert any(x['theorem']=='Snake9.ActualTotal115.actual_total_sum' for x in final['theorem_audits'])
assert sha(progress)==progress_hash and read(progress)==p
snap=H/'audit/total115-completion';snap.mkdir(exist_ok=True)
(snap/'batch-progress.json').write_bytes(progress.read_bytes())
(snap/'ActualTotal115.lean').write_bytes((S/'lean/ActualTotal115.lean').read_bytes())
(snap/'ActualTotal115-audit.json').write_bytes((S/'data/ActualTotal115-audit.json').read_bytes())
archive=H/'certificates/total115-completed-receipts.tar.gz';assert not archive.exists()
members=[]
with archive.open('xb') as out:
    with gzip.GzipFile(fileobj=out,mode='wb',mtime=0) as z:
        with tarfile.open(fileobj=z,mode='w|') as tar:
            for f in sorted(files):
                name=f.relative_to(S).as_posix();info=tar.gettarinfo(str(f),arcname=name)
                info.mtime=0;info.uid=info.gid=0;info.uname=info.gname=''
                with f.open('rb') as inp:tar.addfile(info,inp)
                members.append(dict(path=name,bytes=f.stat().st_size,sha256=sha(f)))
assert archive.stat().st_size<100000000
expected={x['path']:x for x in members}
with tarfile.open(archive,'r:gz') as tar:
    for info in tar:
        row=expected.pop(info.name);f=tar.extractfile(info);d=hashlib.sha256();n=0
        for b in iter(lambda:f.read(1048576),b''):d.update(b);n+=len(b)
        assert (d.hexdigest(),n)==(row['sha256'],row['bytes'])
assert not expected
record=dict(status='PASS_COMPLETE_TOTAL115_RECEIPT_AND_DEPENDENCY_AUDIT',recorded_at=datetime.datetime.now(datetime.timezone.utc).isoformat(),
    checked_modules=1397,axiom_reports=len(reports),final_theorem='Snake9.ActualTotal115.actual_total_sum',
    statement='Every fitting canonical012310 window of an arbitrary Q9 snake has five internal counts summing to at least19.',
    additional_count_or_parity_hypotheses=False,final_axioms=final['theorem_audits'],
    modules=rows,dependencies=dependency_pins,archive=archive.relative_to(H).as_posix(),archive_sha256=sha(archive),
    archive_bytes=archive.stat().st_size,archive_members=members,proof_source='115 data/total-plan.json and its exact archived export',
    source_files_sha256={f.relative_to(R).as_posix():sha(f) for f in [Path(__file__),progress,planpath,S/'scripts/run_batch.py',S/'scripts/check_modules.py',S/'lean/ActualTotal115.lean',S/'data/ActualTotal115-audit.json']},
    seconds=time.monotonic()-start,compiler_rerun=False,new_global_bound=False,
    scope='Completed actual-snake local theorem. All1397 receipt/source/object/log hashes and recorded dependencies rechecked; exact successful receipts/logs/source snapshots archived. No improved global upper bound follows alone.')
target=H/'data/total115-completion.json';assert not target.exists();target.write_text(json.dumps(record,indent=2)+'\n')
print(json.dumps({k:record[k] for k in ['status','checked_modules','axiom_reports','archive_bytes','seconds']}),flush=True)
