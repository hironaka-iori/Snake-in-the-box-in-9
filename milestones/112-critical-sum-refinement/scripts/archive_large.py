"""Create lossless transport copies; retain every original raw proof locally."""
from pathlib import Path
import gzip,hashlib,json,shutil
HERE=Path(__file__).resolve().parents[1]
def digest(p):
    h=hashlib.sha256()
    with p.open('rb') as f:
        for chunk in iter(lambda:f.read(1024*1024),b''):h.update(chunk)
    return h.hexdigest()
record=HERE/'data/large-artifact-archives.json';assert not record.exists()
for filename in ['012340-middle5-outer17-solver.json','012314-upper2-outer18-solver.json']:
    assert json.loads((HERE/'data'/filename).read_text())['status']!='RUNNING'
rows=[]
for p in sorted((HERE/'work').rglob('*')):
    if not p.is_file() or p.stat().st_size<=10000000:continue
    before=digest(p);out=HERE/'archives'/p.relative_to(HERE);out=out.with_name(out.name+'.gz');out.parent.mkdir(parents=True,exist_ok=True)
    assert not out.exists()
    with p.open('rb') as source,out.open('wb') as destination:
        with gzip.GzipFile(filename='',mode='wb',fileobj=destination,mtime=0,compresslevel=6) as compressed:
            shutil.copyfileobj(source,compressed,1024*1024)
    h=hashlib.sha256()
    with gzip.open(out,'rb') as f:
        for chunk in iter(lambda:f.read(1024*1024),b''):h.update(chunk)
    assert h.hexdigest()==before==digest(p)
    rows.append(dict(original=p.relative_to(HERE).as_posix(),bytes=p.stat().st_size,sha256=before,
        archive=out.relative_to(HERE).as_posix(),archive_bytes=out.stat().st_size,archive_sha256=digest(out)))
out=dict(status='LOSSLESS_ARCHIVES_VERIFIED_ORIGINALS_RETAINED',files=rows,
    scope='Original raw files remain on this machine. Git stores these verified gzip copies instead of the large originals. Decompress to each recorded original path before replaying that artifact elsewhere.')
record.write_text(json.dumps(out,indent=2)+'\n');print('Archived',len(rows),'files;',sum(r['bytes'] for r in rows),'original bytes;',sum(r['archive_bytes'] for r in rows),'archive bytes')
