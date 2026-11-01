"""Restore exact archived inputs without replacing different local contents."""
from pathlib import Path
import gzip,hashlib,json,tarfile
HERE=Path(__file__).resolve().parents[1];OUT=HERE/'share-proof'
sha=lambda b:hashlib.sha256(b).hexdigest()
meta=json.loads((HERE/'data/archive.json').read_text())
def save(path,data):
 path.parent.mkdir(parents=True,exist_ok=True)
 if path.exists():assert path.read_bytes()==data, f'Different existing file: {path}'
 else:path.write_bytes(data)
archive=HERE/meta['lean_archive']['path'];assert sha(archive.read_bytes())==meta['lean_archive']['sha256']
with tarfile.open(archive,'r:gz') as tf:
 for member in tf.getmembers():
  assert member.isfile() and not member.issym() and not member.islnk()
  target=(OUT/member.name).resolve();assert target.is_relative_to(OUT.resolve())
  save(target,tf.extractfile(member).read())
for r in meta['native']:
 z=HERE/r['path'];assert sha(z.read_bytes())==r['sha256']
 data=gzip.decompress(z.read_bytes());assert sha(data)==r['raw_sha256']
 save(HERE/'build'/z.name.removesuffix('.gz'),data)
for r in meta['compact']:
 z=OUT/r['path'];assert sha(z.read_bytes())==r['sha256']
 data=gzip.decompress(z.read_bytes());assert sha(data)==r['raw_sha256']
 save(z.with_suffix(''),data)
print('Archived sources and certificate inputs match or have been restored.')
