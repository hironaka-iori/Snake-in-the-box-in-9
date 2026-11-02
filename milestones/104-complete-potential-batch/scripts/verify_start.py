"""Verify the immutable launch files, without treating the active batch as complete."""
from pathlib import Path
import hashlib,json,subprocess,sys
HERE=Path(__file__).resolve().parents[1];ROOT=HERE.parents[1]
manifest=HERE/'data/start-manifest.json';rows=json.loads(manifest.read_text())['files']
for r in rows:
    raw=(ROOT/r['path']).read_bytes()
    assert len(raw)==r['bytes'] and hashlib.sha256(raw).hexdigest()==r['sha256'],r['path']
if '--staged' in sys.argv:
    names=[r['path'] for r in rows]+[manifest.relative_to(ROOT).as_posix()]
    actual=subprocess.check_output(['git','-c','core.commitGraph=false','diff','--cached','--name-only'],cwd=ROOT,text=True).splitlines()
    assert set(names)==set(actual),'Index differs from launch manifest.'
    index=''.join(subprocess.check_output(['git','-c','core.commitGraph=false','ls-files','-s','--',*names[i:i+50]],cwd=ROOT,text=True) for i in range(0,len(names),50))
    blobs={line.split('\t',1)[1]:line.split()[1] for line in index.splitlines()}
    for name in names:
        raw=(ROOT/name).read_bytes()
        if not name.startswith('milestones/104-'):raw=raw.replace(b'\r\n',b'\n')
        assert hashlib.sha1(b'blob '+str(len(raw)).encode()+b'\0'+raw).hexdigest()==blobs[name],name
print('PASS_EXACT_STAGED_LAUNCH' if '--staged' in sys.argv else 'PASS_LOCAL_LAUNCH_MANIFEST',len(rows))
