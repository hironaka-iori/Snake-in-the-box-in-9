"""Split an oversized exact archive for Git transport; keep the local original."""
from pathlib import Path
import hashlib,json
HERE=Path(__file__).resolve().parents[1];ROOT=HERE.parents[1]
CASE=ROOT/'milestones/73-countfree-share-catalogue/cases/case7302'
path=CASE/'data/pending-checkpoint.json';saved=json.loads(path.read_text())
chunk_size=48*1024*1024
for archive in saved['archives']:
    if archive['bytes']<=95*1024*1024:continue
    source=CASE/archive['path'];parts=[];combined=hashlib.sha256()
    with source.open('rb') as stream:
        index=0
        while raw:=stream.read(chunk_size):
            dest=Path(str(source)+f'.part{index:02d}');digest=hashlib.sha256(raw).hexdigest()
            if dest.exists():assert hashlib.sha256(dest.read_bytes()).hexdigest()==digest
            else:dest.write_bytes(raw)
            combined.update(dest.read_bytes())
            parts.append(dict(path=dest.relative_to(CASE).as_posix(),bytes=len(raw),sha256=digest));index+=1
    assert combined.hexdigest()==archive['sha256']
    assert sum(p['bytes'] for p in parts)==archive['bytes']
    archive['parts']=parts
saved['archive_transport']='Oversized archives are stored in ordered .partNN files in Git. The complete local archive is retained. Run milestone83/scripts/restore_large_archives.py after a fresh checkout, before archive verification.'
selection=json.loads((CASE/'data/lrat-slice-selection.json').read_text())
backup=Path(selection['backup_manifest']).parent
saved['superseded_original_lean_export']=dict(
    path=(backup/'original-lean').as_posix(),
    storage='Local only; excluded from Git archives.',
    hash_manifest=selection['backup_manifest'],
    scope='The original CNF/LRAT and generation/export metadata are archived. All selected Lean sources are archived. The superseded unsliced Lean export remains local; exact regeneration was not rerun in this round and is unnecessary for the selected replay.')
path.write_text(json.dumps(saved,indent=2)+'\n')
print('PASS_SPLIT_ARCHIVE_BYTES',sum(len(r.get('parts',[])) for r in saved['archives']),'parts')
