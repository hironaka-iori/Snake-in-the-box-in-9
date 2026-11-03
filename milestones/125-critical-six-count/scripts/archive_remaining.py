"""Preserve the two remaining terminal timeout traces as lossless portable archives."""
from pathlib import Path
import gzip,hashlib,json,shutil
H=Path(__file__).resolve().parents[1]
def digest(stream):
 h=hashlib.sha256();size=0
 for b in iter(lambda:stream.read(1024*1024),b''):h.update(b);size+=len(b)
 return h.hexdigest(),size
rows=[]
for name in ['0120324-total22-orbit','0120324-total22-positive']:
 record=H/'data'/(name+'-solver.json');j=json.loads(record.read_text());assert j['status']=='TIMEOUT'
 original=H/'work'/name/'full.raw.lrat';packed=original.with_suffix('.lrat.gz')
 with original.open('rb') as f:assert digest(f)==(j['raw_sha256'],j['raw_bytes'])
 assert not packed.exists()
 with original.open('rb') as src,packed.open('xb') as dst:
  with gzip.GzipFile(fileobj=dst,mode='wb',filename='',mtime=0) as z:shutil.copyfileobj(src,z)
 with gzip.open(packed,'rb') as f:assert digest(f)==(j['raw_sha256'],j['raw_bytes'])
 with packed.open('rb') as f:h,n=digest(f)
 rows.append(dict(original=original.relative_to(H).as_posix(),original_sha256=j['raw_sha256'],original_bytes=j['raw_bytes'],
  archive=packed.relative_to(H).as_posix(),archive_sha256=h,archive_bytes=n,
  solver_record=record.relative_to(H).as_posix(),solver_record_sha256=hashlib.sha256(record.read_bytes()).hexdigest()))
out=dict(status='PASS_LOSSLESS_PARTIAL_TRACE_ARCHIVES',archives=rows,originals_retained_locally=True,
 exclude_originals_from_git_manifest=True,script_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
 scope='Incomplete timeout traces only. Decompress each archive to its original relative path and verify the recorded SHA256 before rerunning auditors that require the raw file.')
with (H/'data/partial-proof-archives-extra.json').open('x') as f:json.dump(out,f,indent=2);f.write('\n')
print(out['status'],sum(x['original_bytes'] for x in rows),sum(x['archive_bytes'] for x in rows),flush=True)
