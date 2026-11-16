"""Archive exact serialized models while retaining every raw local model."""
from pathlib import Path
import hashlib,json,zipfile
H=Path(__file__).resolve().parents[1]
archive=H/'data/solver-models.zip';assert not archive.exists()
inventory={}
with zipfile.ZipFile(archive,'w',compression=zipfile.ZIP_DEFLATED,compresslevel=6) as z:
    for p in sorted((H/'data').rglob('*.pbtxt')):
        b=p.read_bytes();inventory[p.relative_to(H/'data').as_posix()]=dict(bytes=len(b),sha256=hashlib.sha256(b).hexdigest());z.writestr(p.relative_to(H/'data').as_posix(),b)
with zipfile.ZipFile(archive) as z:
    assert set(z.namelist())==set(inventory)
    for name,row in inventory.items():assert hashlib.sha256(z.read(name)).hexdigest()==row['sha256']
out=dict(archive=archive.name,archive_sha256=hashlib.sha256(archive.read_bytes()).hexdigest(),files=inventory,scope='Every raw pbtxt remains locally in data/. The exact model bytes are published in solver-models.zip to avoid repeating large text models in Git. Extract into data/ to reproduce their recorded paths. Dynamic cycle cuts, if any, remain in result JSON.')
(H/'data/model-archive.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
print('ARCHIVED_EXACT_MODELS',len(inventory),'bytes',archive.stat().st_size)
