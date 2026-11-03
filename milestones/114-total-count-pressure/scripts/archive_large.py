"""Compress large immutable evidence on temporary storage, retaining all originals."""
from pathlib import Path
import gzip,hashlib,json,shutil,tempfile
HERE=Path(__file__).resolve().parents[1]
def digest(p):
    h=hashlib.sha256()
    with p.open('rb') as f:
        for chunk in iter(lambda:f.read(1024*1024),b''):h.update(chunk)
    return h.hexdigest()
record=HERE/'data/large-artifact-archives.json';assert not record.exists()
for name in ['012310-total18-solver.json','012310-total18-cadical153.json','drat-conversion-bootstrap.json',
             'extracted-core-solver.json','extracted-core-scratch-solver.json','pooled-cuts-solver.json']:
    assert json.loads((HERE/'data'/name).read_text())['status']!='RUNNING'
scratch=Path(tempfile.mkdtemp(prefix='snake114-archives-'));rows=[]
for i,p in enumerate(sorted((HERE/'work').rglob('*'))):
    if not p.is_file() or p.stat().st_size<=10000000:continue
    before=digest(p);out=HERE/'archives'/p.relative_to(HERE);out=out.with_name(out.name+'.gz')
    out.parent.mkdir(parents=True,exist_ok=True);assert not out.exists()
    packed=scratch/(str(i)+'.gz')
    with p.open('rb') as src,packed.open('wb') as dst:
        with gzip.GzipFile(filename='',mode='wb',fileobj=dst,mtime=0,compresslevel=6) as z:shutil.copyfileobj(src,z,1024*1024)
    h=hashlib.sha256()
    with gzip.open(packed,'rb') as f:
        for chunk in iter(lambda:f.read(1024*1024),b''):h.update(chunk)
    assert h.hexdigest()==before==digest(p)
    shutil.copyfile(packed,out);assert digest(out)==digest(packed)
    rows.append(dict(original=p.relative_to(HERE).as_posix(),bytes=p.stat().st_size,sha256=before,
        archive=out.relative_to(HERE).as_posix(),archive_bytes=out.stat().st_size,archive_sha256=digest(out)))
    print('ARCHIVED',p.relative_to(HERE).as_posix(),out.stat().st_size,flush=True)
out=dict(status='LOSSLESS_ARCHIVES_VERIFIED_ORIGINALS_RETAINED',files=rows,
    scope='Large original proof files remain local; verified gzip copies provide lossless transport. Completed, partial and unreplayed evidence retain their distinct statuses in their records.')
record.write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
print('ARCHIVES',len(rows),'compressed bytes',sum(r['archive_bytes'] for r in rows),flush=True)
