"""Hash-checked per-certificate archives of completed Lean sources."""
from pathlib import Path,PurePosixPath
import gzip,hashlib,json,sys,tarfile
HERE=Path(__file__).resolve().parents[1];manifest=HERE/'data/lean-source-archive.json'
sha=lambda raw:hashlib.sha256(raw).hexdigest()
if '--restore' in sys.argv:
 meta=json.loads(manifest.read_text());count=0
 for entry in meta['archives']:
  archive=HERE/entry['archive'];assert sha(archive.read_bytes())==entry['sha256']
  expected={r['path']:r for r in entry['files']}
  with tarfile.open(archive,'r:gz') as tar:
   members=tar.getmembers();assert {m.name for m in members}==set(expected)
   for member in members:
    rel=PurePosixPath(member.name);assert member.isfile() and not rel.is_absolute() and '..' not in rel.parts
    path=HERE/'lean'/member.name;assert path.resolve().is_relative_to((HERE/'lean').resolve())
    data=tar.extractfile(member).read();assert sha(data)==expected[member.name]['sha256']
    if path.exists():assert path.read_bytes()==data,('Existing source differs',member.name)
    else:path.parent.mkdir(parents=True,exist_ok=True);path.write_bytes(data)
    count+=1
 print('Restored or matched',count,'completed source files.')
else:
 audit=json.loads((HERE/'data/proof-audit.json').read_text());groups={'support':['LratFast15.lean']}
 for c in audit['completed']:groups['case'+str(c['case'])]=[k+'.lean' for k in c['source_sha256']]
 archives=[];(HERE/'data/lean-sources').mkdir(exist_ok=True)
 for group,names in groups.items():
  archive=HERE/f'data/lean-sources/{group}.tar.gz';entries=[]
  with archive.open('wb') as out,gzip.GzipFile(filename='',mode='wb',fileobj=out,mtime=0) as gz,tarfile.open(fileobj=gz,mode='w') as tar:
   for name in sorted(names):
    path=HERE/'lean'/name;data=path.read_bytes();entries.append(dict(path=name,bytes=len(data),sha256=sha(data)))
    info=tar.gettarinfo(str(path),arcname=name);info.mtime=0;info.uid=info.gid=0;info.uname=info.gname=''
    with path.open('rb') as source:tar.addfile(info,source)
  archives.append(dict(archive=archive.relative_to(HERE).as_posix(),sha256=sha(archive.read_bytes()),bytes=archive.stat().st_size,files=entries))
 meta=dict(completed_cases=audit['completed_cases'],archives=archives)
 manifest.write_text(json.dumps(meta,indent=2)+'\n');print('Archived',sum(len(r['files']) for r in archives),'sources in',sum(r['bytes'] for r in archives),'bytes.')
