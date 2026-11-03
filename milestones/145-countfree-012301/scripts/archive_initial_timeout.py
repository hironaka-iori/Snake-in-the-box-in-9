"""Preserve the incomplete first conversion trace without treating it as a proof."""
from pathlib import Path
import gzip,hashlib,json,shutil
H=Path(__file__).resolve().parents[1]
record=json.loads((H/'data/conversion.json').read_text())
assert record['status']=='CONVERSION_INCOMPLETE' and record['stop_reason']=='TIMEOUT'
p=H/'work/conversion/raw.lrat';q=H/'data/incomplete-first-conversion.lrat.gz';assert not q.exists()
def digest(stream):
 d=hashlib.sha256();n=0
 for b in iter(lambda:stream.read(1048576),b''):d.update(b);n+=len(b)
 return d.hexdigest(),n
with p.open('rb') as f:before,size=digest(f)
assert before==record['preserved_files_sha256']['raw.lrat']
with p.open('rb') as f,q.open('xb') as target:
 with gzip.GzipFile(fileobj=target,mode='wb',mtime=0) as z:shutil.copyfileobj(f,z,1048576)
with gzip.open(q,'rb') as z:assert digest(z)==(before,size)
with q.open('rb') as f:compressed,csize=digest(f)
j=dict(status='PASS_EXACT_ARCHIVE_OF_INCOMPLETE_CONVERSION',source=p.relative_to(H).as_posix(),source_bytes=size,source_sha256=before,
 archive=q.relative_to(H).as_posix(),archive_bytes=csize,archive_sha256=compressed,original_retained_locally=True,
 scope='The first conversion stopped after180seconds while emitting LRAT. This partial trace is not a complete contradiction proof.')
(H/'data/first-conversion-archive.json').write_text(json.dumps(j,indent=2)+'\n');print(json.dumps(j))
