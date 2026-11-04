"""Prevent Git newline conversion from changing the audited evidence."""
from pathlib import Path
import hashlib,json,subprocess
H=Path(__file__).resolve().parents[1];R=H.parents[1]
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
g=['git','-c','core.commitGraph=false','-c','maintenance.auto=false','-c','gc.auto=0']
manifest=H/'data/file-manifest.json';record=json.loads(manifest.read_text())
paths={x['path'] for x in record['files']}|{manifest.relative_to(R).as_posix()}
staged={p.decode() for p in subprocess.check_output(g+['diff','--cached','--name-only','-z'],cwd=R).split(b'\0') if p}
assert staged==paths
for row in record['files']:assert sha(R/row['path'])==row['sha256'],row['path']
backup=H/'audit/file-manifest-before-attributes.json';assert not backup.exists();backup.write_bytes(manifest.read_bytes())
additions=[H/'.gitattributes',R/'milestones/155-share17-replay/.gitattributes',Path(__file__),backup]
for p in additions:
    assert p.relative_to(R).as_posix() not in paths
    record['files'].append(dict(path=p.relative_to(R).as_posix(),bytes=p.stat().st_size,sha256=sha(p)))
record['files'].sort(key=lambda x:x['path'])
record['publication_repair']='Git staging initially normalized a CRLF JSON file. Byte verification rejected it before commit. Per-milestone -text attributes now preserve the original audited bytes; no proof source or receipt was changed.'
subprocess.run(g+['restore','--staged','--pathspec-from-file='+str(H/'data/stage-paths.nul'),'--pathspec-file-nul'],cwd=R,check=True)
manifest.write_text(json.dumps(record,indent=2)+'\n',encoding='utf-8')
print('PRESERVED_AUDITED_BYTES_AND_RESET_ONLY_MANIFEST_STAGING')
