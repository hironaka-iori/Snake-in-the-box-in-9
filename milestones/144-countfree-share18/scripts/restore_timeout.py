"""Restore the exact incomplete trace after a checkout; never overwrite different bytes."""
from pathlib import Path
import gzip,hashlib,json
H=Path(__file__).resolve().parents[1];j=json.loads((H/'data/timeout-archive.json').read_text())
source=H/j['archive'];target=H/j['source']
assert target.resolve().is_relative_to((H/'work').resolve())
assert hashlib.sha256(source.read_bytes()).hexdigest()==j['archive_sha256']
if target.exists():
 assert target.stat().st_size==j['source_bytes'] and hashlib.sha256(target.read_bytes()).hexdigest()==j['source_sha256']
else:
 target.parent.mkdir(parents=True,exist_ok=True);d=hashlib.sha256()
 with gzip.open(source,'rb') as src,target.open('xb') as out:
  for b in iter(lambda:src.read(1048576),b''):d.update(b);out.write(b)
 assert target.stat().st_size==j['source_bytes'] and d.hexdigest()==j['source_sha256']
print('Exact incomplete trace present; no proof claim.')
