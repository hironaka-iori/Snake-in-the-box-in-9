"""Losslessly archive immutable proof artifacts and generated Lean source trees."""
from pathlib import Path
import gzip,hashlib,json,shutil,tarfile,tempfile
HERE=Path(__file__).resolve().parents[1]
def digest(p):
    h=hashlib.sha256()
    with p.open('rb') as f:
        for b in iter(lambda:f.read(1024*1024),b''):h.update(b)
    return h.hexdigest()
record=HERE/'data/large-artifact-archives.json';assert not record.exists()
assert json.loads((HERE/'data/total-plan.json').read_text())['status']=='NATIVE_EXPORT_SIMULATED_LEAN_PENDING'
for p in (HERE/'data').glob('refine-*.json'):
    assert json.loads(p.read_text())['status']=='UNSAT_TRIMMED_NOT_REPLAYED'
scratch=Path(tempfile.mkdtemp(prefix='snake115-archives-'));rows=[]
for i,p in enumerate(sorted((HERE/'work').rglob('*'))):
    if not p.is_file() or p.stat().st_size<=10000000:continue
    before=digest(p);out=HERE/'archives'/p.relative_to(HERE);out=out.with_name(out.name+'.gz')
    out.parent.mkdir(parents=True,exist_ok=True);assert not out.exists();packed=scratch/(str(i)+'.gz')
    with p.open('rb') as src,packed.open('wb') as dst:
        with gzip.GzipFile(filename='',mode='wb',fileobj=dst,mtime=0,compresslevel=6) as z:shutil.copyfileobj(src,z,1024*1024)
    h=hashlib.sha256()
    with gzip.open(packed,'rb') as f:
        for b in iter(lambda:f.read(1024*1024),b''):h.update(b)
    assert h.hexdigest()==before==digest(p)
    shutil.copyfile(packed,out);assert digest(out)==digest(packed)
    rows.append(dict(original=p.relative_to(HERE).as_posix(),bytes=p.stat().st_size,sha256=before,
        archive=out.relative_to(HERE).as_posix(),archive_bytes=out.stat().st_size,archive_sha256=digest(out)))
    print('ARCHIVED',rows[-1]['original'],rows[-1]['archive_bytes'],flush=True)
sources=sorted([*(HERE/'generated-total-core1').rglob('*.lean'),*(HERE/'lean/Refined115').rglob('*.lean')])
assert len(sources)==2792
bundle=scratch/'generated-sources.tar.gz';members=[]
with bundle.open('wb') as output:
    with gzip.GzipFile(filename='',mode='wb',fileobj=output,mtime=0,compresslevel=6) as zipped:
        with tarfile.open(fileobj=zipped,mode='w|',format=tarfile.USTAR_FORMAT) as tar:
            for p in sources:
                row=dict(path=p.relative_to(HERE).as_posix(),bytes=p.stat().st_size,sha256=digest(p));members.append(row)
                info=tarfile.TarInfo(row['path']);info.size=row['bytes'];info.mode=0o644;info.mtime=0
                with p.open('rb') as src:tar.addfile(info,src)
with tarfile.open(bundle,'r|gz') as tar:
    for row,item in zip(members,tar):
        assert item.name==row['path'] and item.size==row['bytes'] and item.isfile()
        h=hashlib.sha256();stream=tar.extractfile(item)
        for b in iter(lambda:stream.read(1024*1024),b''):h.update(b)
        assert h.hexdigest()==row['sha256']==digest(HERE/row['path'])
parts=[];joined=hashlib.sha256()
with bundle.open('rb') as src:
    index=0
    while block:=src.read(45*1024*1024):
        index+=1;p=HERE/'archives'/f'generated-sources.tar.gz.part{index:03d}';assert not p.exists()
        p.write_bytes(block);expected=hashlib.sha256(block).hexdigest();assert digest(p)==expected
        joined.update(block);parts.append(dict(path=p.relative_to(HERE).as_posix(),bytes=len(block),sha256=expected))
assert joined.hexdigest()==digest(bundle)
result=dict(status='LOSSLESS_ARCHIVES_VERIFIED_ORIGINALS_RETAINED',files=rows,
    source_bundle=dict(format='concatenated gzip-compressed USTAR stream',bytes=bundle.stat().st_size,sha256=digest(bundle),parts=parts,members=members),
    scope='All original proof and generated source files remain local. Concatenate source parts in listed order before gzip/tar decoding. Every restored member must match its exact SHA256; generated files remain unproved until Lean receipts exist.')
record.write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
print('VERIFIED_ARCHIVES',len(rows),'proofs',len(members),'source files',len(parts),'source parts',flush=True)
