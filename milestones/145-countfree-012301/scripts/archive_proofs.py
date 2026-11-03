"""Archive exact terminal proof outputs, including the unsuccessful size experiment."""
from pathlib import Path
import gzip, hashlib, json, shutil, time
H = Path(__file__).resolve().parents[1]
read = lambda p: json.loads(p.read_text(encoding='utf-8-sig'))

def digest(stream):
    d = hashlib.sha256(); n = 0
    for block in iter(lambda: stream.read(1048576), b''):
        d.update(block); n += len(block)
    return d.hexdigest(), n

conversion = read(H/'data/conversion-long.json')
replay = read(H/'data/direct-replay.json')
compact = read(H/'data/compact-certificate.json')
assert conversion['status'] == 'PASS_RUP_ONLY_CONVERSION_DIRECT_REPLAY_PENDING'
assert replay['status'] == 'PASS_COMPLETE_DIRECT_RUP_REPLAY'
assert compact['status'] == 'TIMEOUT'
record = H/'data/proof-archives.json'
assert not record.exists()
start = time.monotonic(); rows = []
for folder, name, label, evidence, complete in [
    ('conversion-long', 'raw.lrat', 'converted-original.lrat.gz', conversion, True),
    ('conversion-long', 'trimmed.lrat', 'converted-trimmed.lrat.gz', conversion, True),
    ('compact', 'raw.lrat', 'incomplete-compact.lrat.gz', compact, False),
]:
    source = H/'work'/folder/name; target = H/'certificates'/label
    target.parent.mkdir(exist_ok=True)
    assert not target.exists()
    with source.open('rb') as f: original_hash, original_size = digest(f)
    assert original_hash == evidence['preserved_files_sha256'][name]
    with source.open('rb') as f, target.open('xb') as out:
        with gzip.GzipFile(fileobj=out, mode='wb', mtime=0) as z:
            shutil.copyfileobj(f, z, 1048576)
    with gzip.open(target, 'rb') as f:
        assert digest(f) == (original_hash, original_size)
    with target.open('rb') as f: archive_hash, archive_size = digest(f)
    row = dict(source=source.relative_to(H).as_posix(), source_sha256=original_hash,
               source_bytes=original_size, archive=target.relative_to(H).as_posix(),
               archive_sha256=archive_hash, archive_bytes=archive_size,
               complete_proof=complete, original_retained_locally=True)
    rows.append(row); print(json.dumps(row), flush=True)
record.write_text(json.dumps(dict(status='PASS_EXACT_ARCHIVES', files=rows,
    seconds=time.monotonic()-start), indent=2)+'\n', encoding='utf-8')
