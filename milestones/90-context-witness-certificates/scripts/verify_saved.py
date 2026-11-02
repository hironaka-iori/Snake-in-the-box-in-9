"""Save and verify exact checkpoint files, excluding build objects and live jobs."""
from pathlib import Path
import hashlib, json, subprocess, sys

HERE = Path(__file__).resolve().parents[1]
ROOT = HERE.parents[1]
sha = lambda b: hashlib.sha256(b).hexdigest()
manifest = HERE / 'data/file-manifest.json'
if '--verify' not in sys.argv and '--staged' not in sys.argv:
    checkpoint = json.loads((HERE / 'data/checkpoint.json').read_text())
    assert checkpoint['status'] == 'PASS_WITNESS_PILOT_AND_GENERIC_FACTORIZATION'
    assert sha((HERE / 'data/proof-summary.json').read_bytes()) == checkpoint['proof_summary_sha256']
    paths = [p for p in HERE.rglob('*') if p.is_file() and p != manifest
             and not ({'build', '__pycache__'} & set(p.relative_to(HERE).parts))]
    geometry = json.loads((HERE / 'data/geometry-observation.json').read_text())
    paths += [ROOT / name for name in geometry['archive_paths']]
    paths += [ROOT / name for name in ['README.md', 'COLLABORATION.md', 'RESEARCH_LEDGER.md',
              'milestones/README.md', 'handoff/README.md', 'handoff/CURRENT_STATUS.md', 'handoff/NEXT_AGENT_PROMPT.md']]
    rows = [dict(path=p.relative_to(ROOT).as_posix(), bytes=p.stat().st_size,
                 sha256=sha(p.read_bytes())) for p in sorted(set(paths))]
    manifest.write_text(json.dumps(dict(status='SAVED_WITNESS90', files=rows,
        scope='Completed milestone90 proofs, exact sources and data, computational plans/profiles, frozen live-job observations, newly observed immutable geometry receipts and current handover. Build objects stay local; no full dependency rebuild.'), indent=2) + '\n')
    print('SAVED_MANIFEST', len(rows), 'files', sum(r['bytes'] for r in rows), 'bytes')
else:
    rows = json.loads(manifest.read_text())['files']
    for row in rows:
        raw = (ROOT / row['path']).read_bytes()
        assert len(raw) == row['bytes'] and sha(raw) == row['sha256'], row['path']
    paper = (ROOT / 'paper/snake9_research.tex').read_bytes()
    assert paper == Path('D:/Codex/2026-10-13/new-chat/outputs/snake9_research.tex').read_bytes()
    assert sha(paper) == json.loads((HERE / 'data/checkpoint.json').read_text())['paper_sha256']
    if '--staged' in sys.argv:
        names = [r['path'] for r in rows] + [manifest.relative_to(ROOT).as_posix()]
        index = ''.join(subprocess.check_output(['git', '-c', 'core.commitGraph=false', 'ls-files', '-s', '--',
                                                *names[i:i+60]], cwd=ROOT, text=True)
                        for i in range(0, len(names), 60))
        blobs = {line.split('\t', 1)[1]: line.split()[1] for line in index.splitlines()}
        for name in names:
            raw = (ROOT / name).read_bytes()
            if not name.startswith(('milestones/89-', 'milestones/90-')):
                raw = raw.replace(b'\r\n', b'\n')
            assert hashlib.sha1(b'blob ' + str(len(raw)).encode() + b'\0' + raw).hexdigest() == blobs[name], name
    print('PASS_EXACT_STAGED_FILES' if '--staged' in sys.argv else 'PASS_LOCAL_MANIFEST', len(rows))
