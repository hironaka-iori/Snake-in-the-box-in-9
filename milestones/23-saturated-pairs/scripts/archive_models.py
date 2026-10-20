"""Losslessly compress model protobuf text, preserving the hashes in original receipts."""
import gzip
import hashlib
import json
from pathlib import Path

HERE=Path(__file__).resolve().parents[1]
def sha(data): return hashlib.sha256(data).hexdigest()

def main():
    out=HERE/'model-archives.json'
    assert not out.exists(), 'Do not overwrite the archive receipt.'
    records=[]
    for p in sorted((HERE/'runs').rglob('*.model.txt')):
        receipt=json.loads(p.with_name(p.name.replace('.model.txt','.json')).read_text(encoding='utf-8'))
        data=p.read_bytes()
        assert sha(data)==receipt['result']['model_sha256']
        dest=p.with_suffix(p.suffix+'.gz')
        assert not dest.exists()
        encoded=gzip.compress(data,compresslevel=9,mtime=0)
        dest.write_bytes(encoded)
        assert gzip.decompress(dest.read_bytes())==data
        records.append(dict(original=str(p.relative_to(HERE)),archive=str(dest.relative_to(HERE)),
            original_bytes=len(data),original_sha256=sha(data),archive_bytes=len(encoded),archive_sha256=sha(encoded)))
        # Exact path of the already-verified duplicate only; no directory deletion.
        p.unlink()
    out.write_text(json.dumps(dict(status='PASS_LOSSLESS',code_sha256=sha(Path(__file__).read_bytes()),files=records),indent=2)+'\n',encoding='utf-8')
    print('models',len(records),'bytes',sum(r['original_bytes'] for r in records),'compressed',sum(r['archive_bytes'] for r in records))

if __name__=='__main__': main()
