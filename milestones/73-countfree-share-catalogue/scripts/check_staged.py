"""Audit exact staged proof bytes, including every archived generated source."""
from pathlib import Path
import hashlib,io,json,subprocess,tarfile
HERE=Path(__file__).resolve().parents[1];ROOT=HERE.parents[1]
sha=lambda b:hashlib.sha256(b).hexdigest();read=lambda p:json.loads(p.read_text())
def staged(path):
    return subprocess.check_output(['git','-c','core.commitGraph=false','show',':'+path.relative_to(ROOT).as_posix()],cwd=ROOT)
cases=[]
for manifest_path in sorted((HERE/'cases').glob('*/data/archive.json')):
    out=manifest_path.parent.parent;manifest=read(manifest_path);audit_path=out/'data/proof-audit.json';audit=read(audit_path)
    assert sha(staged(audit_path))==manifest['audit_sha256']
    entry=manifest['lean_archive'];data=staged(out/entry['path']);assert sha(data)==entry['sha256']
    found={}
    with tarfile.open(fileobj=io.BytesIO(data),mode='r:gz') as tf:
        for item in tf.getmembers():
            assert item.isfile()
            name=Path(item.name).relative_to('lean').with_suffix('').as_posix()
            assert name not in found;found[name]=sha(tf.extractfile(item).read())
    assert found==audit['source_sha256']
    for entry in manifest['compact']:assert sha(staged(out/entry['path']))==entry['sha256']
    cases.append(dict(case_number=manifest['case_number'],archived_modules=len(found)))
tracked=subprocess.check_output(['git','ls-files','--',HERE.relative_to(ROOT).as_posix()],cwd=ROOT,text=True).splitlines()
exact=[]
for rel in tracked:
    path=ROOT/rel
    if path.suffix in ['.lean','.json','.log','.gz'] and path.name!='staged-proof-audit.json':
        assert staged(path)==path.read_bytes(),f'Git changed audited bytes: {rel}'
        exact.append(rel)
result=dict(status='PASS_STAGED_PROOF_BYTES',cases=cases,exact_staged_files=len(exact),
    scope='All indexed Lean, JSON, log and compressed-evidence bytes match the local checkpoint; archived sources match the completed proof audits.')
(HERE/'data/staged-proof-audit.json').write_text(json.dumps(result,indent=2)+'\n');print(result,flush=True)
