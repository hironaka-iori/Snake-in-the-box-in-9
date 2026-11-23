import gzip,hashlib,shutil
from pathlib import Path
d=Path(__file__).resolve().parent
for folder in (d/'bounds',d/'tight'):
    for p in sorted(folder.glob('*.tree')):
        if folder.name=='tight' and not p.with_suffix('.result').exists():continue
        dst=p.with_suffix('.tree.gz')
        data=p.read_bytes()
        if not dst.exists():
            comp=gzip.compress(data,compresslevel=6,mtime=0)
            assert gzip.decompress(comp)==data
            dst.write_bytes(comp)
        assert gzip.decompress(dst.read_bytes())==data
        p.unlink()
