"""Audit and archive the completed prefix of the ongoing129 replay."""
from pathlib import Path
import gzip,hashlib,json,subprocess,tarfile,datetime
H=Path(__file__).resolve().parents[1];R=H.parents[1];P=R/'milestones/129-fourth-count-three'
read=lambda p:json.loads(p.read_text(encoding='utf-8-sig'))
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
out=H/'data/replay129-archives.json';assert not out.exists()
raw=(P/'data/replay-progress.json').read_bytes();j=json.loads(raw)
snap=H/'audit/observed-replay129.json';assert not snap.exists();snap.write_bytes(raw)
assert [x['module'] for x in j['checked_modules']]==j['ordered_modules'][:len(j['checked_modules'])]
selected=set();receipts=[]
for row in j['checked_modules']:
 name=row['module'];cnf=name=='Recovered129G.LocalWindowCnf.Triple129'
 rp=P/'data'/('independent-core-cnf-audit.json' if cnf else name+'-audit.json');q=read(rp)
 assert sha(rp)==row['receipt_sha256'] and q['exit_code']==0 and not q.get('timeout',False)
 src=P/'lean'/(name.replace('.','/')+'.lean');obj=P/'build-replay'/(name.replace('.','/')+'.olean')
 assert sha(src)==q['source_sha256'] and sha(obj)==q['importable_object_sha256' if cnf else 'olean_sha256']
 log=Path(q['log']);log=log if log.is_absolute() else P/log;assert sha(log)==q['log_sha256']
 ss=log.parent/'source.lean.txt' if cnf else P/q['source_snapshot'];assert sha(ss)==q['source_sha256']
 for n,d in q['dependencies'].items():
  p=Path(n);p=p if p.is_absolute() else R/p;assert sha(p)==d,n
 for a in q.get('theorem_audits',[]):assert set(a['axioms'])<={'propext','Classical.choice','Quot.sound'}
 selected.update([rp,src,obj,log,ss]);receipts.append(dict(module=name,receipt=rp.relative_to(R).as_posix(),sha256=sha(rp)))
 checker=ss.parent/'checker.py.txt'
 if checker.exists():selected.add(checker)
tracked=set(subprocess.check_output(['git','-c','core.commitGraph=false','ls-files','-z','--','milestones/129-fourth-count-three'],cwd=R).decode().split('\0'))
files=[dict(path=p.relative_to(R).as_posix(),bytes=p.stat().st_size,sha256=sha(p)) for p in sorted(selected) if p.relative_to(R).as_posix() not in tracked]
groups=[[]];size=0
for x in files:
 if groups[-1] and size+x['bytes']>90000000:groups.append([]);size=0
 groups[-1].append(x);size+=x['bytes']
arcs=[]
for i,group in enumerate(groups):
 if not group:continue
 p=H/'archives'/f'replay129-prefix-{i+1}.tar.gz'
 with p.open('xb') as outstream:
  with gzip.GzipFile(filename='',mode='wb',fileobj=outstream,mtime=0,compresslevel=6) as z:
   with tarfile.open(fileobj=z,mode='w|',format=tarfile.PAX_FORMAT) as tar:
    for x in group:
     info=tarfile.TarInfo(x['path']);info.size=x['bytes'];info.mode=0o644;info.mtime=0
     with (R/x['path']).open('rb') as f:tar.addfile(info,f)
 with tarfile.open(p,'r:gz') as tar:
  members=tar.getmembers();assert [m.name for m in members]==[x['path'] for x in group]
  for m,x in zip(members,group):
   assert m.isfile() and m.size==x['bytes']
   with tar.extractfile(m) as f:assert hashlib.sha256(f.read()).hexdigest()==x['sha256']
 assert p.stat().st_size<100000000
 arcs.append(dict(path=p.relative_to(H).as_posix(),bytes=p.stat().st_size,sha256=sha(p),files=group))
record=dict(status='PASS_AUDITED_REPLAY_PREFIX_ARCHIVES',recorded_at=datetime.datetime.now(datetime.timezone.utc).isoformat(),
 observed_status=j['status'],observed_pid=j['pid'],snapshot_sha256=sha(snap),checked_modules=len(receipts),total_modules=j['total_modules'],
 complete_refutation_at_snapshot=j['status']=='PASS_COMPLETE_CNF_REFUTATION',receipts=receipts,archives=arcs,
 script_sha256=sha(Path(__file__)),scope='Exact checked prefix at snapshot time. A partial prefix does not establish the contradiction or its actual-snake consequence.')
out.write_text(json.dumps(record,indent=2)+'\n',encoding='utf-8')
print(json.dumps(dict(checked=len(receipts),total=j['total_modules'],archived_files=len(files),archive_bytes=sum(x['bytes'] for x in arcs))))
