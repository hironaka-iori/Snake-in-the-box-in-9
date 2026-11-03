"""Preserve audited endpoint completion files absent from the repository index."""
from pathlib import Path
import gzip,hashlib,json,subprocess,tarfile
H=Path(__file__).resolve().parents[1];R=H.parents[1]
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
review=H/'data/endpoint122-completion-review.json';j=json.loads(review.read_text())
assert j['status']=='PASS_448_ENDPOINT_MODULE_RECEIPTS_AND_ACTUAL_ASSEMBLY'
tracked=set(subprocess.check_output(['git','-c','core.commitGraph=false','ls-files','-z','--','milestones/122-endpoint-equality'],cwd=R).decode().split('\0'))
rows=[]
for name,digest in j['source_files_sha256'].items():
 p=Path(name);p=p if p.is_absolute() else R/p
 if not p.is_relative_to(R/'milestones/122-endpoint-equality'):continue
 rel=p.relative_to(R).as_posix();assert sha(p)==digest
 if rel not in tracked:rows.append(dict(path=rel,sha256=digest,bytes=p.stat().st_size))
rows.sort(key=lambda x:x['path']);groups=[[]];size=0
for x in rows:
 if groups[-1] and size+x['bytes']>90000000:groups.append([]);size=0
 groups[-1].append(x);size+=x['bytes']
archives=[]
for i,group in enumerate(groups):
 dest=H/'archives'/f'endpoint122-completion-{i+1}.tar.gz'
 with dest.open('xb') as out:
  with gzip.GzipFile(filename='',mode='wb',fileobj=out,mtime=0,compresslevel=6) as gz:
   with tarfile.open(fileobj=gz,mode='w|',format=tarfile.PAX_FORMAT) as tar:
    for x in group:
     info=tarfile.TarInfo(x['path']);info.size=x['bytes'];info.mode=0o644;info.mtime=0
     with (R/x['path']).open('rb') as f:tar.addfile(info,f)
 with tarfile.open(dest,'r:gz') as tar:
  members=tar.getmembers();assert [x.name for x in members]==[x['path'] for x in group]
  for member,x in zip(members,group):
   assert member.isfile() and member.size==x['bytes']
   with tar.extractfile(member) as f:assert hashlib.sha256(f.read()).hexdigest()==x['sha256']
 assert dest.stat().st_size<100000000
 archives.append(dict(path=dest.relative_to(H).as_posix(),sha256=sha(dest),bytes=dest.stat().st_size,files=group))
out=H/'data/endpoint122-archives.json';assert not out.exists()
out.write_text(json.dumps(dict(status='PASS_LOSSLESS_ENDPOINT_COMPLETION_ARCHIVES',review_sha256=sha(review),
 script_sha256=sha(Path(__file__)),archives=archives),indent=2)+'\n',encoding='utf-8')
print(json.dumps(dict(files=len(rows),raw_bytes=sum(x['bytes'] for x in rows),archive_bytes=sum(x['bytes'] for x in archives),archives=len(archives))))
