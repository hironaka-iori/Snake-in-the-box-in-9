"""Preserve the large incomplete trace in a verified compressed publication copy."""
from pathlib import Path
import gzip,hashlib,json
H=Path(__file__).resolve().parents[1]
record=json.loads((H/'data/native-base.json').read_text())
assert record['status']=='TIMEOUT'
p=H/'work/certificate-base/raw.lrat';out=H/'data/timedout-trace.lrat.gz'
assert not out.exists()
d=hashlib.sha256()
with p.open('rb') as src,out.open('xb') as target:
 with gzip.GzipFile(filename='',mode='wb',fileobj=target,compresslevel=3,mtime=0) as compressed:
  for b in iter(lambda:src.read(1048576),b''):d.update(b);compressed.write(b)
assert d.hexdigest()==record['raw_sha256']
d2=hashlib.sha256();n=0
with gzip.open(out,'rb') as f:
 for b in iter(lambda:f.read(1048576),b''):d2.update(b);n+=len(b)
assert d2.hexdigest()==d.hexdigest() and n==p.stat().st_size
j=dict(status='PASS_EXACT_COMPRESSED_TIMEOUT_TRACE',source='work/certificate-base/raw.lrat',source_bytes=n,source_sha256=d.hexdigest(),archive='data/timedout-trace.lrat.gz',archive_bytes=out.stat().st_size,archive_sha256=hashlib.sha256(out.read_bytes()).hexdigest(),original_retained_locally=True,scope='Incomplete trace from a timed-out run. It establishes no contradiction. The compressed copy reproduces every original byte.')
(H/'data/timeout-archive.json').write_text(json.dumps(j,indent=2)+'\n',encoding='utf-8');print(json.dumps(j))
