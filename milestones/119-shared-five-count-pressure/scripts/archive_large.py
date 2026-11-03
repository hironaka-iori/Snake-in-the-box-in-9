"""Preserve all large native proof bytes in verified lossless transport archives."""
from pathlib import Path
import gzip,hashlib,json,shutil,tempfile
HERE=Path(__file__).resolve().parents[1]
def digest(p):
    h=hashlib.sha256()
    with p.open('rb') as f:
        for block in iter(lambda:f.read(1024*1024),b''):h.update(block)
    return h.hexdigest()
record=HERE/'data/large-artifact-archives.json';assert not record.exists()
for name in ['012304-conditional-a-total22-full-solver.json','012304-completed-b-total22-full-solver.json']:
    assert json.loads((HERE/'data'/name).read_text())['status']!='RUNNING'
scratch=Path(tempfile.mkdtemp(prefix='snake119-archives-'));rows=[]
for i,path in enumerate(sorted((HERE/'work').rglob('*'))):
    if not path.is_file() or path.stat().st_size<=10000000:continue
    before=digest(path);target=HERE/'archives'/path.relative_to(HERE)
    target=target.with_name(target.name+'.gz');target.parent.mkdir(parents=True,exist_ok=True)
    assert not target.exists();packed=scratch/(str(i)+'.gz')
    with path.open('rb') as src,packed.open('wb') as dst:
        with gzip.GzipFile(filename='',mode='wb',fileobj=dst,mtime=0,compresslevel=6) as z:shutil.copyfileobj(src,z,1024*1024)
    h=hashlib.sha256()
    with gzip.open(packed,'rb') as stream:
        for block in iter(lambda:stream.read(1024*1024),b''):h.update(block)
    assert h.hexdigest()==before==digest(path)
    shutil.copyfile(packed,target);assert digest(target)==digest(packed)
    rows.append(dict(original=path.relative_to(HERE).as_posix(),bytes=path.stat().st_size,sha256=before,
        archive=target.relative_to(HERE).as_posix(),archive_bytes=target.stat().st_size,archive_sha256=digest(target)))
    print('ARCHIVED',path.relative_to(HERE).as_posix(),target.stat().st_size,flush=True)
record.write_text(json.dumps(dict(status='LOSSLESS_ARCHIVES_VERIFIED_ORIGINALS_RETAINED',files=rows,
    scope='All original native proofs remain local. Verified gzip archives preserve exact bytes for Git transport; native proof and pending Lean status remain distinct.'),indent=2)+'\n',encoding='utf-8')
print('ARCHIVES',len(rows),'compressed bytes',sum(row['archive_bytes'] for row in rows),flush=True)
