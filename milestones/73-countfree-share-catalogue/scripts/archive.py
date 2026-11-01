"""Pack audited case sources and compact proofs without altering their bytes."""
from pathlib import Path
import gzip,hashlib,io,json,sys,tarfile
HERE=Path(__file__).resolve().parents[1]
sha=lambda b:hashlib.sha256(b).hexdigest()
for number in map(int,sys.argv[1:]):
    out=HERE/'cases'/f'case{number}'
    audit=json.loads((out/'data/proof-audit.json').read_text())
    assert audit['status']=='PASS_LOCAL_SHARE_THEOREM'
    sources=sorted((out/'lean').rglob('*.lean'))
    actual={p.relative_to(out/'lean').with_suffix('').as_posix():sha(p.read_bytes()) for p in sources}
    assert actual==audit['source_sha256']
    stream=io.BytesIO()
    with tarfile.open(fileobj=stream,mode='w') as tf:
        for p in sources:
            data=p.read_bytes();info=tarfile.TarInfo(p.relative_to(out).as_posix())
            info.size=len(data);info.mode=0o644;info.mtime=0
            tf.addfile(info,io.BytesIO(data))
    archive=out/'data/lean-sources.tar.gz'
    archive.write_bytes(gzip.compress(stream.getvalue(),compresslevel=9,mtime=0))
    compact=[]
    for ext in ['cnf','lrat']:
        p=out/f'certificates/share{number}.{ext}';raw=p.read_bytes();z=p.with_suffix(p.suffix+'.gz')
        z.write_bytes(gzip.compress(raw,compresslevel=9,mtime=0))
        compact.append(dict(path=z.relative_to(out).as_posix(),sha256=sha(z.read_bytes()),raw_sha256=sha(raw),raw_bytes=len(raw)))
    manifest=dict(case_number=number,status='ARCHIVED_CHECKED_LOCAL_THEOREM',
        audit_sha256=sha((out/'data/proof-audit.json').read_bytes()),
        lean_archive=dict(path=archive.relative_to(out).as_posix(),sha256=sha(archive.read_bytes()),modules=len(sources)),
        compact=compact,scope='Exact sources and compact refutation. Native input evidence remains in milestone72; inherited support builds are reused.')
    (out/'data/archive.json').write_text(json.dumps(manifest,indent=2)+'\n')
    print(number,'archived',len(sources),'Lean modules',flush=True)
