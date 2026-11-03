"""Preserve a terminal native trace as a verified lossless gzip archive."""
from pathlib import Path
import gzip,hashlib,json,sys
H=Path(__file__).resolve().parents[1]
name=sys.argv[1];assert name in ['augmented','reduced']
record=H/'data'/('search.json' if name=='augmented' else 'search-reduced.json')
j=json.loads(record.read_text());assert j['status']!='RUNNING'
raw=H/'work'/(name+'.raw.lrat');arc=H/'archives'/(name+'.raw.lrat.gz');arc.parent.mkdir(exist_ok=True)
meta=H/'data'/('archive-'+name+'.json');assert not arc.exists() and not meta.exists()
def digest(f):
 h=hashlib.sha256();n=0
 for b in iter(lambda:f.read(1024*1024),b''):h.update(b);n+=len(b)
 return h.hexdigest(),n
with raw.open('rb') as f:original=digest(f)
assert original==(j['raw_sha256'],j['raw_bytes'])
with raw.open('rb') as src,arc.open('wb') as out:
 with gzip.GzipFile(filename='',mode='wb',fileobj=out,mtime=0,compresslevel=6) as dest:
  for b in iter(lambda:src.read(1024*1024),b''):dest.write(b)
with gzip.open(arc,'rb') as f:assert digest(f)==original
with arc.open('rb') as f:compressed=digest(f)
out=dict(status='PASS_LOSSLESS_NATIVE_TRACE_ARCHIVE',original=raw.relative_to(H).as_posix(),original_sha256=original[0],original_bytes=original[1],archive=arc.relative_to(H).as_posix(),archive_sha256=compressed[0],archive_bytes=compressed[1],solver_status=j['status'],script_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),scope='Byte preservation only; incomplete traces do not establish contradictions.')
meta.write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8');print(json.dumps(out,indent=2))
