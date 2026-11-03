"""Compress a terminal partial proof without removing or changing its original bytes."""
from pathlib import Path
import gzip,hashlib,json,shutil
H=Path(__file__).resolve().parents[1]
p=H/'work/0120324-total24-orbit/full.raw.lrat'
record=H/'data/0120324-total24-orbit-solver.json'
j=json.loads(record.read_text());assert j['status']=='TIMEOUT'
def digest(stream):
 h=hashlib.sha256()
 for b in iter(lambda:stream.read(1024*1024),b''):h.update(b)
 return h.hexdigest()
with p.open('rb') as f:assert digest(f)==j['raw_sha256']
out=p.with_suffix(p.suffix+'.gz');assert not out.exists()
with p.open('rb') as src,out.open('xb') as dst:
 with gzip.GzipFile(fileobj=dst,mode='wb',filename='',mtime=0) as z:shutil.copyfileobj(src,z)
with gzip.open(out,'rb') as f:assert digest(f)==j['raw_sha256']
with out.open('rb') as f:compressed=digest(f)
meta=dict(status='PASS_LOSSLESS_PARTIAL_PROOF_ARCHIVE',original=p.relative_to(H).as_posix(),
 original_bytes=p.stat().st_size,original_sha256=j['raw_sha256'],archive=out.relative_to(H).as_posix(),
 archive_bytes=out.stat().st_size,archive_sha256=compressed,
 original_retained_locally=True,exclude_original_from_git_manifest=True,
 reason='The timeout trace exceeds the GitHub file size limit. It contains no complete contradiction.',
 restoration='Decompress the gzip archive to the recorded original relative path; verify the recorded SHA256.',
 script_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
 solver_record_sha256=hashlib.sha256(record.read_bytes()).hexdigest())
target=H/'data/partial-proof-archive.json'
with target.open('x') as f:json.dump(meta,f,indent=2);f.write('\n')
print(meta['status'],meta['original_bytes'],meta['archive_bytes'],flush=True)
