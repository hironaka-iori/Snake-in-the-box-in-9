"""Restore archived proof bytes under this milestone; verify existing originals."""
from pathlib import Path
import gzip, hashlib, json, shutil
H = Path(__file__).resolve().parents[1]
read = lambda p: json.loads(p.read_text(encoding='utf-8-sig'))

def sha(p):
    d = hashlib.sha256()
    with p.open('rb') as f:
        for block in iter(lambda: f.read(1048576), b''): d.update(block)
    return d.hexdigest()

rows = read(H/'data/proof-archives.json')['files'] + [read(H/'data/first-conversion-archive.json')]
for row in rows:
    source = (H/row['source']).resolve(); archive = (H/row['archive']).resolve()
    assert source.is_relative_to(H) and archive.is_relative_to(H)
    assert sha(archive) == row['archive_sha256']
    if source.exists():
        assert source.stat().st_size == row['source_bytes'] and sha(source) == row['source_sha256']
        continue
    source.parent.mkdir(parents=True, exist_ok=True)
    pending = source.with_suffix(source.suffix+'.restoring')
    with gzip.open(archive, 'rb') as f, pending.open('xb') as out:
        shutil.copyfileobj(f, out, 1048576)
    assert pending.stat().st_size == row['source_bytes'] and sha(pending) == row['source_sha256']
    pending.replace(source)
print('PASS_EXACT_RESTORE_OR_EXISTING_BYTES')
