"""Verify staged proof sources and archives against the completed audit."""
from pathlib import Path
import hashlib,io,json,subprocess,tarfile
HERE=Path(__file__).resolve().parents[1];ROOT=HERE.parents[2];OUT=HERE/'share-proof'
sha=lambda b:hashlib.sha256(b).hexdigest();read=lambda p:json.loads(p.read_text())
def staged(path):
 rel=path.relative_to(ROOT).as_posix()
 return subprocess.check_output(['git','-c','core.commitGraph=false','show',':'+rel],cwd=ROOT)
audit=read(OUT/'data/proof-audit.json');assert audit['status']=='PASS_LOCAL_SHARE_THEOREM'
assert staged(OUT/'data/proof-audit.json')==(OUT/'data/proof-audit.json').read_bytes()
archive=read(HERE/'data/archive.json');entry=archive['lean_archive'];data=staged(HERE/entry['path']);assert sha(data)==entry['sha256']
found={}
with tarfile.open(fileobj=io.BytesIO(data),mode='r:gz') as tf:
 for item in tf.getmembers():
  name=Path(item.name).relative_to('lean').with_suffix('').as_posix()
  found[name]=sha(tf.extractfile(item).read())
assert found==audit['source_sha256']
tracked=subprocess.check_output(['git','ls-files','--',str((OUT/'lean').relative_to(ROOT))],cwd=ROOT,text=True).splitlines()
count=0
for rel in tracked:
 path=ROOT/rel
 if path.suffix!='.lean':continue
 name=path.relative_to(OUT/'lean').with_suffix('').as_posix();assert sha(staged(path))==audit['source_sha256'][name];count+=1
for r in archive['native']:assert sha(staged(HERE/r['path']))==r['sha256']
for r in archive['compact']:assert sha(staged(OUT/r['path']))==r['sha256']
out=dict(status='PASS_STAGED_PROOF_BYTES',archived_lean_modules=len(found),directly_tracked_lean_modules=count,native_archives=len(archive['native']),compact_archives=len(archive['compact']),scope='Git index bytes match the completed source audit and evidence archive hashes.')
(HERE/'data/staged-proof-audit.json').write_text(json.dumps(out,indent=2)+'\n');print(out)
