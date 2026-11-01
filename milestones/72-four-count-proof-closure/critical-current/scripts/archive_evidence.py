"""Preserve exact native evidence and generated Lean sources with hashes."""
from pathlib import Path
import gzip,hashlib,json,tarfile
HERE=Path(__file__).resolve().parents[1];OUT=HERE/'share-proof'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest();read=lambda p:json.loads(p.read_text())
(HERE/'certificates').mkdir(exist_ok=True)
native=[]
for f in sorted((HERE/'data').glob('*-certificate.json')):
 m=read(f)
 if m['status']!='NATIVE_DRAT_VERIFIED' or 'shape_index' not in m:continue
 tag=f.name.removesuffix('-certificate.json')
 for ext,key in [('cnf','cnf_sha256'),('core.cnf','core_sha256'),('drat','drat_sha256')]:
  src=HERE/f'build/{tag}.{ext}';dest=HERE/f'certificates/{tag}.{ext}.gz'
  assert sha(src)==m[key]
  if not dest.exists() or hashlib.sha256(gzip.decompress(dest.read_bytes())).hexdigest()!=m[key]:
   dest.write_bytes(gzip.compress(src.read_bytes(),compresslevel=9,mtime=0))
  native.append(dict(path=str(dest.relative_to(HERE)).replace('\\','/'),sha256=sha(dest),raw_sha256=sha(src),raw_bytes=src.stat().st_size))
sources=sorted((OUT/'lean').rglob('*.lean'));archive=OUT/'data/lean-sources.tar.gz'
with tarfile.open(archive,'w:gz') as tf:
 for f in sources:tf.add(f,arcname=str(f.relative_to(OUT)).replace('\\','/'))
compact=[]
for name in ['share12.cnf','share12.lrat']:
 f=OUT/'certificates'/name;z=f.with_suffix(f.suffix+'.gz')
 z.write_bytes(gzip.compress(f.read_bytes(),compresslevel=9,mtime=0))
 compact.append(dict(path=str(z.relative_to(OUT)).replace('\\','/'),sha256=sha(z),raw_sha256=sha(f)))
out=dict(native=native,lean_archive=dict(path=str(archive.relative_to(HERE)).replace('\\','/'),sha256=sha(archive),files=len(sources),bytes=archive.stat().st_size),compact=compact,scope='Exact evidence archive. Consult proof-audit.json for verification status; archive presence alone does not establish a theorem.')
(HERE/'data/archive.json').write_text(json.dumps(out,indent=2)+'\n')
print('Archived',len(native),'native files and',len(sources),'Lean sources.')
