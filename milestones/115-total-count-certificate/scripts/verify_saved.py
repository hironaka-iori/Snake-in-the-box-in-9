"""Freeze or verify the exact package; optionally restore lossless source/proof archives."""
from pathlib import Path,PurePosixPath
import gzip,hashlib,json,shutil,subprocess,sys,tarfile,tempfile
HERE=Path(__file__).resolve().parents[1];ROOT=HERE.parents[1]
read=lambda p:json.loads(p.read_text(encoding='utf-8-sig'))
def digest(p):
    h=hashlib.sha256()
    with p.open('rb') as f:
        for b in iter(lambda:f.read(1024*1024),b''):h.update(b)
    return h.hexdigest()
def stream_digest(f):
    h=hashlib.sha256();n=0
    for b in iter(lambda:f.read(1024*1024),b''):h.update(b);n+=len(b)
    return n,h.hexdigest()
archives=read(HERE/'data/large-artifact-archives.json')
assert archives['status']=='LOSSLESS_ARCHIVES_VERIFIED_ORIGINALS_RETAINED'
originals={r['original'] for r in archives['files']}|{r['path'] for r in archives['source_bundle']['members']}
restore='--restore-archives' in sys.argv
freeze=not any(x in sys.argv for x in ['--restore-archives','--verify','--staged'])
for r in archives['files']:
    packed,raw=HERE/r['archive'],HERE/r['original']
    assert packed.resolve().is_relative_to(HERE.resolve()) and raw.resolve().is_relative_to(HERE.resolve())
    assert packed.stat().st_size==r['archive_bytes'] and digest(packed)==r['archive_sha256']
    if restore or freeze:
        with gzip.open(packed,'rb') as src:assert stream_digest(src)==(r['bytes'],r['sha256'])
        if restore and not raw.exists():
            raw.parent.mkdir(parents=True,exist_ok=True)
            with gzip.open(packed,'rb') as src,raw.open('xb') as dst:shutil.copyfileobj(src,dst,1024*1024)
        if raw.exists():assert raw.stat().st_size==r['bytes'] and digest(raw)==r['sha256']
bundle=archives['source_bundle'];whole=hashlib.sha256();size=0
scratch=Path(tempfile.mkdtemp(prefix='snake115-restore-')) if restore or freeze else None
joined=scratch/'sources.tar.gz' if scratch else None
output=joined.open('xb') if joined else None
try:
    for part in bundle['parts']:
        p=HERE/part['path'];assert p.stat().st_size==part['bytes'] and digest(p)==part['sha256']
        with p.open('rb') as src:
            for b in iter(lambda:src.read(1024*1024),b''):
                whole.update(b);size+=len(b)
                if output:output.write(b)
finally:
    if output:output.close()
assert size==bundle['bytes'] and whole.hexdigest()==bundle['sha256']
if joined:
    seen=set()
    with tarfile.open(joined,'r|gz') as tar:
        iterator=iter(tar)
        for row in bundle['members']:
            item=next(iterator);relative=PurePosixPath(item.name)
            assert item.name==row['path'] and item.isfile() and item.size==row['bytes']
            assert not relative.is_absolute() and '..' not in relative.parts and item.name not in seen
            seen.add(item.name);target=HERE/item.name;assert target.resolve().is_relative_to(HERE.resolve())
            src=tar.extractfile(item);h=hashlib.sha256();n=0
            dst=None
            if restore and not target.exists():target.parent.mkdir(parents=True,exist_ok=True);dst=target.open('xb')
            try:
                for b in iter(lambda:src.read(1024*1024),b''):
                    h.update(b);n+=len(b)
                    if dst:dst.write(b)
            finally:
                if dst:dst.close()
            assert (n,h.hexdigest())==(row['bytes'],row['sha256'])
            if target.exists():assert target.stat().st_size==row['bytes'] and digest(target)==row['sha256']
        assert next(iterator,None) is None
    assert len(seen)==len(bundle['members'])==2792
if restore:
    print('PASS_ARCHIVES_RESTORED_OR_ALREADY_PRESENT',len(originals));sys.exit(0)
checkpoint=read(HERE/'data/checkpoint.json');summary=read(HERE/'data/proof-summary.json')
assert checkpoint['status']=='PASS_PROGRESS_WITH_TWO_LIVE_LEAN_BATCHES'
assert digest(ROOT/checkpoint['prior_checkpoint'])==checkpoint['prior_checkpoint_sha256']
assert digest(HERE/'data/proof-summary.json')==checkpoint['proof_summary_sha256']
for rel,h in summary['source_files_sha256'].items():assert digest(HERE/rel)==h,rel
assert not checkpoint['new_global_bound'] and not checkpoint['full_lean_contradiction_checked']
assert checkpoint['new_mathematical_definitions']==0
assert digest(ROOT/'paper/snake9_research.tex')==checkpoint['paper_sha256']
editor=Path('D:/Codex/2026-10-13/new-chat/outputs/snake9_research.tex')
if editor.exists():assert digest(editor)==checkpoint['paper_sha256']
manifest=HERE/'data/file-manifest.json'
if freeze:
    assert not manifest.exists();paths=[]
    checked={m['module'] for m in summary['modules']}
    for p in HERE.rglob('*'):
        if not p.is_file():continue
        rel=p.relative_to(HERE);name=rel.as_posix()
        if name in originals or '__pycache__' in rel.parts or any(x.startswith('build') for x in rel.parts[:-1]):continue
        if rel.parts[0]=='logs':continue
        if name in ['data/check.lock','data/batch.lock','data/batch-progress.json']:continue
        if rel.parts[0]=='data' and p.name.endswith('-audit.json'):
            data=read(p)
            if data.get('module') and data['module'] not in checked:continue
        paths.append(p)
    for p in (HERE/'logs').glob('*'):
        if not p.is_file():continue
        if p.name.startswith(('core0.','core1.','core2.','unsat0.')):paths.append(p)
        elif p.name.startswith('export-total-') and p.suffix=='.json':
            assert read(p)['status'] in ['GENERATED_SEMANTICS_NOT_CHECKED','NATIVE_EXPORT_SIMULATED_LEAN_PENDING'];paths.append(p)
    paths += [ROOT/p for p in read(HERE/'data/additional-evidence.json')]
    paths += [ROOT/p for p in ['README.md','COLLABORATION.md','RESEARCH_LEDGER.md','milestones/README.md',
                              'handoff/README.md','handoff/CURRENT_STATUS.md','handoff/NEXT_AGENT_PROMPT.md']]
    rows=[dict(path=p.relative_to(ROOT).as_posix(),bytes=p.stat().st_size,sha256=digest(p)) for p in sorted(set(paths))]
    assert all(r['bytes']<100*1024*1024 for r in rows)
    manifest.write_text(json.dumps(dict(status='SAVED_CONCRETE_SEMANTICS_AND_DISTINCT_DIRECTION_RESEARCH',files=rows,
        archive_policy='Original proofs and2792generated source files remain local and have verified lossless transport archives; restore before compiling a fresh checkout.',
        live_policy='Live process state, locks and logs are excluded. Dated process-verified observations and completed receipts are frozen.'),indent=2)+'\n',encoding='utf-8')
    print('SAVED_MANIFEST',len(rows),'files',sum(r['bytes'] for r in rows),'bytes')
else:
    rows=read(manifest)['files']
    for r in rows:
        p=ROOT/r['path'];assert p.stat().st_size==r['bytes'] and digest(p)==r['sha256'],r['path']
    if '--staged' in sys.argv:
        names=[r['path'] for r in rows]+[manifest.relative_to(ROOT).as_posix()]
        actual=subprocess.check_output(['git','-c','core.commitGraph=false','diff','--cached','--name-only'],cwd=ROOT,text=True).splitlines()
        assert set(actual)==set(names),'Index differs from reviewed manifest'
        index=''.join(subprocess.check_output(['git','-c','core.commitGraph=false','ls-files','-s','--',*names[i:i+35]],cwd=ROOT,text=True) for i in range(0,len(names),35))
        blobs={line.split('\t',1)[1]:line.split()[1] for line in index.splitlines()}
        for name in names:
            raw=(ROOT/name).read_bytes()
            if not name.startswith(('milestones/104-','milestones/115-')):raw=raw.replace(b'\r\n',b'\n')
            assert hashlib.sha1(b'blob '+str(len(raw)).encode()+b'\0'+raw).hexdigest()==blobs[name],name
    print('PASS_EXACT_STAGED_FILES' if '--staged' in sys.argv else 'PASS_LOCAL_MANIFEST',len(rows))
