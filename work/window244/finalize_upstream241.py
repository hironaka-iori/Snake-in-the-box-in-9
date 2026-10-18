"""Recheck all completed objects and preserve source-only 241 evidence."""
import hashlib,json,pathlib,re,tarfile
ROOT=pathlib.Path(__file__).resolve().parents[2]
build=ROOT/'work/spectral/.verification/upstream241-7d41890'
out=ROOT/'outputs/window244/upstream241';out.mkdir(parents=True,exist_ok=True)
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
state=json.loads((build/'manifest.json').read_bytes())
assert state['status']=='SUCCESS_INDEPENDENT_191_241'
allowed={'propext','Classical.choice','Quot.sound'}
targets={'Snake9.upper_bound_242','Snake9.upper_bound_241','Snake9.verified_interval_191_241'}
assert set(state['final_axioms'])==targets
assert all(set(v)<=allowed for v in state['final_axioms'].values())
inventory=[]
for name in state['module_order']:
    src=build/(name.replace('.','/')+'.lean');obj=src.with_suffix('.olean')
    log=build/'logs'/(name+'.log');rec=state['modules'][name]
    assert rec['exit_code']==0 and not rec['memory_exceeded'],name
    assert sha(src)==state['sources'][name]['sha256']==rec['identity']['source_sha256'],name
    assert sha(obj)==rec['olean_sha256'] and sha(log)==rec['log_sha256'],name
    for dep,h in rec['identity']['imports'].items():
        assert sha(build/(dep.replace('.','/')+'.olean'))==h,(name,dep)
    inventory.extend([src,log])
audit=build/'logs/IndependentAudit.log'
assert sha(audit)==state['final_audit_sha256']
assert sha(ROOT/'work/window244/review_upstream241.py')==state['driver_sha256']
for src in [build/'ReviewCheckAppend.lean',build/'ReviewSemanticAppend.lean']:
    original=ROOT/'work/window244'/('CheckAppend.lean' if 'CheckAppend' in src.name else 'SemanticAppend.lean')
    assert sha(src)==sha(original)
(out/'manifest.json').write_bytes((build/'manifest.json').read_bytes())
(out/'IndependentAudit.log').write_bytes(audit.read_bytes())
archive=out/'sources-and-logs.tar.gz'
with tarfile.open(archive,'w:gz') as tar:
    for path in inventory+[audit,build/'manifest.json',build/'IndependentAudit.lean']:
        tar.add(path,arcname=path.relative_to(build).as_posix())
summary=dict(status=state['status'],upstream_commit=state['upstream_commit'],
    completed_utc=state['completed_utc'],modules=len(state['module_order']),
    original_custom_modules=1238,lean_version='4.19.0',mathlib_commit=state['mathlib_commit'],
    final_axioms=state['final_axioms'],peak_bytes=max(state['modules'][n]['peak_bytes'] for n in state['module_order']),
    limit_mib=1800,all_source_object_import_and_log_hashes_rechecked=True,
    manifest_sha256=sha(out/'manifest.json'),audit_sha256=sha(audit),
    archive_sha256=sha(archive),archive_bytes=archive.stat().st_size,
    scope='Independent source reconstruction with documented equivalent proof decomposition; no custom object cache')
(out/'verification.json').write_bytes((json.dumps(summary,indent=2)+'\n').encode())
print(json.dumps(summary,indent=2))
