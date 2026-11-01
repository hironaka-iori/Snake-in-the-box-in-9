"""Verify saved local evidence and exact Git-index bytes in one index read."""
from pathlib import Path
import hashlib
import json
import subprocess

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
sha = lambda data: hashlib.sha256(data).hexdigest()
manifest = json.loads((HERE / 'file-manifest.json').read_text())
for row in manifest['files']:
    data = (ROOT / row['path']).read_bytes()
    assert len(data) == row['bytes'] and sha(data) == row['sha256'], row['path']
prefixes = ['milestones/73-countfree-share-catalogue',
            'milestones/74-graph-interpretation-audit', 'handoff/2026-11-02']
raw = subprocess.check_output(['git', '-c', 'core.commitGraph=false',
                               'ls-files', '--stage', '-z', '--', *prefixes], cwd=ROOT)
checked = []
for record in raw.decode().split('\0'):
    if not record:
        continue
    metadata, relative = record.split('\t', 1)
    mode, oid, stage = metadata.split()
    assert stage == '0'
    path = ROOT / relative
    is_proof = path.suffix in ['.lean', '.json', '.log', '.gz']
    is_new_script = path.suffix == '.py' and (
        relative.startswith(prefixes[1]) or relative.startswith(prefixes[2]) or
        path.name in ['slice_lrat.py', 'checkpoint_pending.py'])
    if not (is_proof or is_new_script) or path.name == 'staged-evidence.json':
        continue
    data = path.read_bytes()
    blob_id = hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest()
    assert blob_id == oid, 'Staged bytes differ from audited local bytes: '+relative
    checked.append(relative)
result = dict(status='PASS_LOCAL_MANIFEST_AND_STAGED_EVIDENCE',
              manifested_files=len(manifest['files']), exact_staged_files=len(checked),
              manifest_sha256=sha((HERE / 'file-manifest.json').read_bytes()),
              files=checked,
              scope='Exact local manifest and Git blob identity for indexed proof/evidence files and new scripts. Does not add a theorem or rebuild inherited proofs.')
(HERE / 'staged-evidence.json').write_text(json.dumps(result, indent=2)+'\n')
print(result['status'], result['manifested_files'], 'manifest files;', len(checked), 'exact staged files')
