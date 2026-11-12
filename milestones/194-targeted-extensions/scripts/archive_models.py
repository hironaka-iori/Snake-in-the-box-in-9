from pathlib import Path
import hashlib,json,zipfile
H=Path(__file__).resolve().parents[1];target=H/'data/solver-models.zip';assert not target.exists()
files=sorted((H/'data').glob('*.pbtxt'));records=[]
with zipfile.ZipFile(target,'w',compression=zipfile.ZIP_DEFLATED,compresslevel=6) as archive:
    for path in files:
        name=path.relative_to(H).as_posix();digest=hashlib.sha256(path.read_bytes()).hexdigest()
        archive.write(path,name);records.append(dict(entry=name,sha256=digest,bytes=path.stat().st_size))
with zipfile.ZipFile(target) as archive:
    assert archive.namelist()==[r['entry'] for r in records]
    for row in records:assert hashlib.sha256(archive.read(row['entry'])).hexdigest()==row['sha256']
(H/'data/solver-model-archive.json').write_text(json.dumps(dict(models=len(files),archive_sha256=hashlib.sha256(target.read_bytes()).hexdigest(),raw_bytes=sum(r['bytes'] for r in records),archive_bytes=target.stat().st_size,entries=records,instructions='Extract solver-models.zip into this milestone folder before replay. Raw models remain available locally; the archive is the Git publication copy.'),indent=2)+'\n')
print('ARCHIVED_MODELS',len(files),'bytes',target.stat().st_size)
