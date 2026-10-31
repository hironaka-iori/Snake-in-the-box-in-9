"""Preserve native candidates with original and compressed byte hashes."""
from pathlib import Path
import gzip,hashlib,json,sys
HERE=Path(__file__).resolve().parents[1];manifest=HERE/'data/certificate-archives.json'
sha=lambda b:hashlib.sha256(b).hexdigest()
if '--restore' in sys.argv:
    for row in json.loads(manifest.read_text()):
        blob=(HERE/row['archive']).read_bytes();assert sha(blob)==row['archive_sha256']
        raw=gzip.decompress(blob);assert sha(raw)==row['sha256']
        target=HERE/row['file'];assert target.resolve().is_relative_to((HERE/'build').resolve());target.parent.mkdir(exist_ok=True)
        if target.exists():assert target.read_bytes()==raw
        else:target.write_bytes(raw)
else:
    out=[];(HERE/'certificates').mkdir(exist_ok=True)
    for name in ['share0','share0-cap119']:
        for ext in ['cnf','core.cnf','drat']:
            p=HERE/'build'/f'{name}.{ext}';raw=p.read_bytes();blob=gzip.compress(raw,mtime=0);target=HERE/'certificates'/(p.name+'.gz');target.write_bytes(blob)
            out.append(dict(file=p.relative_to(HERE).as_posix(),archive=target.relative_to(HERE).as_posix(),sha256=sha(raw),archive_sha256=sha(blob),bytes=len(raw)))
    manifest.write_text(json.dumps(out,indent=2)+'\n')
print('Candidate archive hashes checked.')
