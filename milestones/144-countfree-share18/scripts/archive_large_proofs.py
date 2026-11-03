"""Create verified compressed copies of fixed proof files larger than90MB."""
from pathlib import Path
import gzip,hashlib,json
H=Path(__file__).resolve().parents[1]
index=H/'data/large-proof-archives.json';assert not index.exists()
files=[]
for folder in ['work/certificate-alternative','certificates']:
 for p in sorted((H/folder).glob('*')):
  if not p.is_file() or p.stat().st_size<90000000:continue
  relative=p.relative_to(H).as_posix();out=H/'data'/('archive-'+relative.replace('/','_')+'.gz');assert not out.exists()
  d=hashlib.sha256()
  with p.open('rb') as src,out.open('xb') as dst:
   with gzip.GzipFile(filename='',mode='wb',fileobj=dst,compresslevel=3,mtime=0) as z:
    for b in iter(lambda:src.read(1048576),b''):d.update(b);z.write(b)
  check=hashlib.sha256();n=0
  with gzip.open(out,'rb') as src:
   for b in iter(lambda:src.read(1048576),b''):check.update(b);n+=len(b)
  assert n==p.stat().st_size and check.hexdigest()==d.hexdigest()
  files.append(dict(source=relative,source_bytes=n,source_sha256=d.hexdigest(),archive=out.relative_to(H).as_posix(),archive_bytes=out.stat().st_size,archive_sha256=hashlib.sha256(out.read_bytes()).hexdigest()))
assert files
index.write_text(json.dumps(dict(status='PASS_EXACT_LARGE_PROOF_ARCHIVES',files=files,originals_retained_locally=True),indent=2)+'\n',encoding='utf-8')
print(json.dumps(dict(status='PASS_EXACT_LARGE_PROOF_ARCHIVES',files=len(files),original_bytes=sum(r['source_bytes'] for r in files),compressed_bytes=sum(r['archive_bytes'] for r in files))))
