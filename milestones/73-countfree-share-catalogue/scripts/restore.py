"""Restore missing archived sources and compact proofs, rejecting changed files."""
from pathlib import Path
import gzip,hashlib,io,json,sys,tarfile
HERE=Path(__file__).resolve().parents[1]
sha=lambda b:hashlib.sha256(b).hexdigest()
def save_missing(path,data):
    if path.exists():assert path.read_bytes()==data,f'Existing bytes differ: {path}'
    else:path.parent.mkdir(parents=True,exist_ok=True);path.write_bytes(data)
for number in map(int,sys.argv[1:]):
    out=(HERE/'cases'/f'case{number}').resolve();manifest=json.loads((out/'data/archive.json').read_text())
    audit=json.loads((out/'data/proof-audit.json').read_text())
    assert sha((out/'data/proof-audit.json').read_bytes())==manifest['audit_sha256']
    entry=manifest['lean_archive'];data=(out/entry['path']).read_bytes();assert sha(data)==entry['sha256']
    seen={}
    with tarfile.open(fileobj=io.BytesIO(data),mode='r:gz') as tf:
        for item in tf.getmembers():
            path=(out/item.name).resolve()
            assert path.is_relative_to(out/'lean') and item.isfile()
            raw=tf.extractfile(item).read();name=path.relative_to(out/'lean').with_suffix('').as_posix()
            assert sha(raw)==audit['source_sha256'][name];seen[name]=sha(raw)
            save_missing(path,raw)
    assert seen==audit['source_sha256']
    for entry in manifest['compact']:
        path=out/entry['path'];data=path.read_bytes();assert sha(data)==entry['sha256']
        raw=gzip.decompress(data);assert sha(raw)==entry['raw_sha256'];save_missing(path.with_suffix(''),raw)
    print(number,'restored or matched',len(seen),'sources and compact proof',flush=True)
