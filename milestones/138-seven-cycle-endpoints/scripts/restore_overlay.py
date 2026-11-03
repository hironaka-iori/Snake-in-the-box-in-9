"""Restore missing generic Lean module objects without duplicating their bytes."""
from pathlib import Path
import hashlib,json,os,time,shutil
H=Path(__file__).resolve().parents[1];R=H.parents[1]
record=H/'data/module-overlay.json'
def sha(p):
 h=hashlib.sha256()
 with p.open('rb') as f:
  for b in iter(lambda:f.read(8*1024*1024),b''):h.update(b)
 return h.hexdigest()
if record.exists():
 j=json.loads(record.read_text())
 for row in j['files']:
  src,dst=Path(row['source']),Path(row['destination'])
  assert sha(src)==row['sha256']
  if not dst.exists():dst.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(src,dst)
  assert sha(dst)==row['sha256']
 print('Verified/restored',len(j['files']),'objects')
else:
 e=R/'milestones/125-critical-six-count/data/environment-sum.json'
 env=json.loads(e.read_text());build=H/'build-base';rows=[];t=time.monotonic()
 for root in env['paths']:
  for prefix in ['LocalWindowCnf','LocalWindowSat','LocalWindowUnsat']:
   source=Path(root)/prefix
   if not source.exists():continue
   for src in sorted(source.rglob('*.olean')):
    dst=build/src.relative_to(Path(root))
    if dst.exists():continue
    digest=sha(src);dst.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(src,dst)
    assert sha(dst)==digest
    rows.append(dict(source=str(src),destination=str(dst),bytes=src.stat().st_size,sha256=digest))
 j=dict(status='PASS_MISSING_MODULE_OBJECT_OVERLAY',environment_sha256=sha(e),script_sha256=sha(Path(__file__)),files=rows,seconds=time.monotonic()-t,scope='Exact existing compiled dependencies copied in original search-path order to fill missing names beneath newly shadowing root namespaces. Existing generated objects untouched. These reproducible copies are excluded from the new checkpoint file manifest; this receipt and restoration script are retained.')
 record.write_text(json.dumps(j,indent=2)+'\n',encoding='utf-8')
 print(json.dumps(dict(status=j['status'],objects=len(rows),bytes=sum(r['bytes'] for r in rows),seconds=j['seconds'])))
