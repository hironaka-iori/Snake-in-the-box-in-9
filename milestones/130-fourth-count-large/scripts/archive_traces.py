"""Preserve both incomplete traces without upgrading their proof status."""
from pathlib import Path
import gzip,hashlib,json
H=Path(__file__).resolve().parents[1]
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
meta=H/'data/trace-archives.json';assert not meta.exists()
review=json.loads((H/'data/large-review.json').read_text());rows=[]
def digest(f):
 h=hashlib.sha256();n=0
 for b in iter(lambda:f.read(1048576),b''):h.update(b);n+=len(b)
 return h.hexdigest(),n
for name,status in [('large','INTERRUPTED_NO_TERMINAL_STATUS'),('large-resumed','TIMEOUT')]:
 src=H/'work'/(name+'.raw.lrat');dst=H/'archives'/(name+'.raw.lrat.gz')
 with src.open('rb') as f:original=digest(f)
 with src.open('rb') as f,dst.open('xb') as out:
  with gzip.GzipFile(filename='',mode='wb',fileobj=out,mtime=0,compresslevel=6) as z:
   for b in iter(lambda:f.read(1048576),b''):z.write(b)
 with gzip.open(dst,'rb') as f:assert digest(f)==original
 assert dst.stat().st_size<100000000
 rows.append(dict(original=src.relative_to(H).as_posix(),original_sha256=original[0],original_bytes=original[1],
  archive=dst.relative_to(H).as_posix(),archive_sha256=sha(dst),archive_bytes=dst.stat().st_size,native_status=status))
meta.write_text(json.dumps(dict(status='PASS_LOSSLESS_INCOMPLETE_TRACE_ARCHIVES',files=rows,
 script_sha256=sha(Path(__file__)),review_sha256=sha(H/'data/large-review.json')),indent=2)+'\n',encoding='utf-8')
print(json.dumps(dict(files=len(rows),raw_bytes=sum(x['original_bytes'] for x in rows),archive_bytes=sum(x['archive_bytes'] for x in rows))))
