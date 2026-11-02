"""Independent byte and completed-receipt audit for milestone95."""
from pathlib import Path
import hashlib,json,re

HERE=Path(__file__).resolve().parents[1];ROOT=HERE.parents[1]
read=lambda p:json.loads(p.read_text(encoding='utf-8-sig'))
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
plan=read(HERE/'data/port-plan.json')
assert plan['status']=='PREPARED_IMPORT_AND_NAMESPACE_PORTS_NOT_COMPILED'
assert sha(ROOT/plan['generator'])==plan['generator_sha256']
assert not plan['duplicate_audit']['collisions']
imports=re.compile(rb'^(?:\xef\xbb\xbf)?[ \t]*import[ \t]+[^\r\n]*(?:\r?\n|$)',re.M)
token=re.compile(rb"(?<![A-Za-z0-9_'])CountPropagation65(?![A-Za-z0-9_'])")
for name,row in plan['modules'].items():
    old=ROOT/row['original_source'];new=ROOT/row['port_source']
    assert sha(old)==row['original_source_sha256'],name
    assert sha(new)==row['port_source_sha256'],name
    assert token.sub(b'CountPropagationPort95',imports.sub(b'',old.read_bytes()))==imports.sub(b'',new.read_bytes()),name
assert len(plan['modules'])==46

completed=[]
for receipt in sorted((HERE/'data').glob('*-audit.json')):
    r=read(receipt)
    if r.get('status')!='PASS_COMPATIBLE_CREDIT_MODULE':continue
    name=r['module'];src=HERE/'lean'/(name+'.lean')
    assert r['exit_code']==0 and not r['timeout']
    assert sha(src)==r['source_sha256'] and sha(HERE/'build'/(name+'.olean'))==r['olean_sha256']
    assert sha(HERE/r['log'])==r['log_sha256']
    snapshot=HERE/r['source_snapshot']
    assert snapshot.read_bytes()==src.read_bytes()
    assert sha(snapshot.parent/'checker.py.txt')==r['checker_sha256']
    for dep,digest in r['dependencies'].items():assert sha(ROOT/dep)==digest,dep
    assert not re.search(r'\b(sorry|admit|native_decide)\b',src.read_text())
    assert src.read_text().count('#print axioms')==len(r['theorem_audits'])
    for a in r['theorem_audits']:assert set(a['axioms'])<={'propext','Classical.choice','Quot.sound'}
    completed.append(dict(module=name,receipt=receipt.relative_to(ROOT).as_posix(),receipt_sha256=sha(receipt),theorem_audits=len(r['theorem_audits'])))

out=dict(status='PASS_CURRENT_SAVED_SOURCES_AND_RECEIPTS',port_modules=46,modules=completed,
         theorem_audits=sum(r['theorem_audits'] for r in completed),
         port_plan_sha256=sha(HERE/'data/port-plan.json'),script_sha256=sha(Path(__file__)),
         scope='Exact import/namespace transformations and successful receipt bytes; uncompleted sources remain unchecked.')
(HERE/'data/source-audit.json').write_text(json.dumps(out,indent=2)+'\n')
print(out['status'],len(completed),'modules;',out['theorem_audits'],'audits')
