"""Preserve the inconclusive stronger query with byte-verified archive members."""
from pathlib import Path
import hashlib,json,zipfile
H=Path(__file__).resolve().parents[1]; S=H/'strengthening'; R=H.parents[1]
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
read=lambda p:json.loads(p.read_text(encoding='utf-8-sig'))
native=read(S/'data/native-queries.json')
assert native['status']=='BOUNDED_NATIVE_QUERIES_FINISHED'
assert len(native['queries'])==1 and native['queries'][0]['status']=='TIMEOUT'
folder=S/'work/universal17'
run=read(folder/'solver-run.json'); assert run['status']=='TIMEOUT'
assert run['timeout_seconds']==60 and run['exit_code']!=20
enc=read(folder/'encoding.json')
assert enc['share_cap']==16 and enc['target_share']==17 and enc['extra_clauses']==0
assert sha(folder/'input.cnf')==enc['cnf_sha256']
files=sorted(p for p in folder.rglob('*') if p.is_file())
archive=H/'archives/strengthening-timeout152.zip';archive.parent.mkdir(exist_ok=True);assert not archive.exists()
members=[]
with zipfile.ZipFile(archive,'x',compression=zipfile.ZIP_DEFLATED,compresslevel=6) as z:
    for p in files:
        name=p.relative_to(H).as_posix();z.write(p,name)
        members.append(dict(path=name,bytes=p.stat().st_size,sha256=sha(p)))
with zipfile.ZipFile(archive) as z:
    assert set(z.namelist())=={m['path'] for m in members}
    for m in members:
        data=z.read(m['path'])
        assert len(data)==m['bytes'] and hashlib.sha256(data).hexdigest()==m['sha256']
out=dict(status='PASS_BYTE_VERIFIED_INCONCLUSIVE_QUERY_ARCHIVE',archive=archive.relative_to(H).as_posix(),
         bytes=archive.stat().st_size,sha256=sha(archive),members=members,
         query_outcome='TIMEOUT_UNRESOLVED',uncompressed_bytes=sum(m['bytes'] for m in members),
         original_files_retained=True,solver_seconds=run['seconds'],
         scope='A partial proof log is archived for provenance only. No unsatisfiability, satisfying assignment or share-17 theorem was established.')
target=H/'data/strengthening-archive.json';assert not target.exists()
target.write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
print(json.dumps({k:v for k,v in out.items() if k!='members'}))
