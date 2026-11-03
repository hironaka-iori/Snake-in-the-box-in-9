"""Preserve fixed traces and the unported export, with verified lossless bytes."""
from pathlib import Path
import gzip, hashlib, json

H = Path(__file__).resolve().parents[1]
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
out = H / 'data/archives.json'
assert not out.exists()
files = sorted((H / 'work').glob('*.lrat'))
files += [H / 'work/export/triple129.lrat']
files += sorted((H / 'generated').rglob('*.lean'))
rows = []
def digest(stream):
    h, n = hashlib.sha256(), 0
    for b in iter(lambda: stream.read(1024 * 1024), b''):
        h.update(b)
        n += len(b)
    return h.hexdigest(), n
for src in files:
    rel = src.relative_to(H)
    dest = H / 'archives' / (rel.as_posix() + '.gz')
    dest.parent.mkdir(parents=True, exist_ok=True)
    with src.open('rb') as f:
        original = digest(f)
    with src.open('rb') as inp, dest.open('xb') as outer:
        with gzip.GzipFile(filename='', mode='wb', fileobj=outer, mtime=0, compresslevel=6) as packed:
            for b in iter(lambda: inp.read(1024 * 1024), b''):
                packed.write(b)
    with gzip.open(dest, 'rb') as f:
        assert digest(f) == original
    rows.append(dict(original=rel.as_posix(), original_sha256=original[0], original_bytes=original[1],
                     archive=dest.relative_to(H).as_posix(), archive_sha256=sha(dest), archive_bytes=dest.stat().st_size))
out.write_text(json.dumps(dict(status='PASS_LOSSLESS_EVIDENCE_ARCHIVES', files=rows,
                              script_sha256=sha(Path(__file__))), indent=2) + '\n', encoding='utf-8')
print(json.dumps(dict(files=len(rows), original_bytes=sum(x['original_bytes'] for x in rows),
                      archive_bytes=sum(x['archive_bytes'] for x in rows))))
