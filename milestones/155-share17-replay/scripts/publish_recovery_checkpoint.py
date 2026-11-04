"""Preserve and stage the immutable accepted prefix; omit live progress files."""
from pathlib import Path
import hashlib, json, subprocess, sys
H=Path(__file__).resolve().parents[1];R=H.parents[1]
read=lambda p:json.loads(Path(p).read_text(encoding='utf-8-sig'))
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
git=['git','-c','core.commitGraph=false','-c','maintenance.auto=false','-c','gc.auto=0']
manifest=H/'data/recovery-publication-manifest.json'
protected=read(R/'milestones/154-share17-broader-semantics/data/checkpoint.json')['protected_unrelated_files_sha256']
for p,d in protected.items():assert sha(R/p)==d,p
if not manifest.exists():
    old=read(H/'audit/memory-stop-68/full-replay-progress.json')
    assert old['status']=='STOPPED_ON_FAILED_OR_INCOMPLETE_MODULE' and len(old['checked_modules'])==68
    selected={H/'.gitattributes',H/'MEMORY_RECOVERY.md'}
    selected.update((H/'scripts').glob('*.py'))
    selected.update(p for p in (H/'analysis').iterdir() if p.is_file())
    selected.update(p for p in (H/'audit/memory-stop-68').iterdir() if p.is_file())
    reports=0
    for row in old['checked_modules']:
        rp=H/'data'/(row['module']+'-audit.json');q=read(rp)
        assert sha(rp)==row['receipt_sha256']
        assert q['status']=='PASS' and q['exit_code']==0 and q['stop_reason'] is None
        assert sha(q['source'])==q['source_sha256'] and sha(q['object'])==q['olean_sha256']
        assert sha(q['log'])==q['log_sha256']
        for p,d in q['dependencies'].items():assert sha(p)==d,p
        assert len(q['axioms'])==row['axiom_reports'];reports+=len(q['axioms'])
        assert all(set(x['axioms'])<={'propext','Classical.choice','Quot.sound'} for x in q['axioms'])
        folder=Path(q['log']).parent
        assert sha(folder/'source.lean.txt')==q['source_sha256']
        assert sha(folder/'checker.py.txt')==q['checker_sha256']
        selected.update([rp,Path(q['source']),Path(q['log']),folder/'source.lean.txt',folder/'checker.py.txt',folder/'record.json'])
    note=(''+
        '# Research checkpoint: 68 share-17 replay modules accepted\n\n'
        'The complete replay remains unfinished. Its next compiler launch stopped\n'
        'at the memory check; 68 accepted modules and their exact evidence are\n'
        'preserved. A recovery process waits for sufficient memory before one\n'
        'resumption attempt. Inspect its live state before starting another job.\n'
        'Read milestones/155-share17-replay/MEMORY_RECOVERY.md. The final local\n'
        'theorem, paper update and any new global bound remain pending.\n\n'
        'Historical updates follow.\n\n')
    for name in ['README.md','RESEARCH_LEDGER.md','COLLABORATION.md']:
        p=R/name;raw=p.read_bytes();assert not raw.startswith(note.encode())
        p.write_bytes(note.encode()+raw);selected.add(p)
    cp=H/'data/resource-recovery-checkpoint.json'
    assert not cp.exists()
    checkpoint=dict(status='PASS_ACCEPTED68_PREFIX_WITH_MEMORY_RECOVERY_PENDING',
        base_commit=subprocess.check_output(git+['rev-parse','HEAD'],cwd=R,text=True).strip(),
        accepted_modules=68,axiom_reports=reports,final_replay_modules=137,
        complete_contradiction=False,actual_snake_share17_complete=False,new_global_upper_bound=False,
        paper_unchanged=True,paper_sha256=sha(R/'paper/snake9_research.tex'),
        archived_progress_sha256=sha(H/'audit/memory-stop-68/full-replay-progress.json'),
        protected_unrelated_files_sha256=protected,
        live_progress_excluded=True,
        range_arithmetic_Lean_status='PENDING' if not (H/'analysis/range-lean-check.json').exists() else 'See accepted receipt')
    cp.write_text(json.dumps(checkpoint,indent=2)+'\n',encoding='utf-8',newline='\n');selected.add(cp)
    rows=[dict(path=p.relative_to(R).as_posix(),bytes=p.stat().st_size,sha256=sha(p)) for p in sorted(selected)]
    assert all(x['bytes']<90_000_000 for x in rows)
    manifest.write_text(json.dumps(dict(status='EXACT_ACCEPTED68_RECOVERY_PUBLICATION',files=rows),indent=2)+'\n',encoding='utf-8',newline='\n')
rows=read(manifest)['files']
for row in rows:assert sha(R/row['path'])==row['sha256'],row['path']
paths=[x['path'] for x in rows]+[manifest.relative_to(R).as_posix()]
if '--stage' in sys.argv:
    assert not subprocess.check_output(git+['diff','--cached','--name-only'],cwd=R,text=True).strip()
    pathlist=H/'data/recovery-stage-paths.nul';pathlist.write_bytes(b'\0'.join(p.encode() for p in paths)+b'\0')
    subprocess.run(git+['add','-f','--pathspec-from-file='+str(pathlist),'--pathspec-file-nul'],cwd=R,check=True)
if '--stage' in sys.argv or '--check-staged' in sys.argv:
    staged={p.decode() for p in subprocess.check_output(git+['diff','--cached','--name-only','-z'],cwd=R).split(b'\0') if p}
    assert staged<=set(paths),staged-set(paths)
    child=subprocess.Popen(git+['cat-file','--batch'],cwd=R,stdin=subprocess.PIPE,stdout=subprocess.PIPE)
    for path in paths:
        child.stdin.write((':'+path+'\n').encode());child.stdin.flush()
        header=child.stdout.readline().decode().split();assert len(header)==3 and header[1]=='blob',header
        count=int(header[2]);digest=hashlib.sha256()
        while count:
            data=child.stdout.read(min(count,1048576));assert data;digest.update(data);count-=len(data)
        assert child.stdout.read(1)==b'\n' and digest.hexdigest()==sha(R/path),path
    child.stdin.close();assert child.wait()==0
print(json.dumps(dict(status='PASS_EXACT_RECOVERY_CHECKPOINT_FILES',files=len(paths),bytes=sum(x['bytes'] for x in rows))))
