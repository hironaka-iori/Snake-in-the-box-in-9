"""Restore missing exact proofs from verified archives without overwriting different bytes."""
from pathlib import Path
import gzip,hashlib,json
H=Path(__file__).resolve().parents[1]
def sha(p):
 d=hashlib.sha256()
 with p.open('rb') as f:
  for b in iter(lambda:f.read(1048576),b''):d.update(b)
 return d.hexdigest()
for r in json.loads((H/'data/large-proof-archives.json').read_text())['files']:
 source=H/r['archive'];target=H/r['source'];assert target.resolve().is_relative_to(H.resolve())
 assert sha(source)==r['archive_sha256']
 if target.exists():assert target.stat().st_size==r['source_bytes'] and sha(target)==r['source_sha256']
 else:
  target.parent.mkdir(parents=True,exist_ok=True);d=hashlib.sha256()
  with gzip.open(source,'rb') as src,target.open('xb') as dst:
   for b in iter(lambda:src.read(1048576),b''):d.update(b);dst.write(b)
  assert target.stat().st_size==r['source_bytes'] and d.hexdigest()==r['source_sha256']
print('Exact proof files present; theorem status is recorded separately.')
