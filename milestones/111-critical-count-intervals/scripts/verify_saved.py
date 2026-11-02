"""Freeze exact evidence, verify saved/staged bytes, or restore missing raw proofs."""
from pathlib import Path
import gzip, hashlib, json, re, shutil, subprocess, sys

HERE = Path(__file__).resolve().parents[1]
ROOT = HERE.parents[1]
read = lambda p: json.loads(p.read_text(encoding='utf-8-sig'))
sha = lambda b: hashlib.sha256(b).hexdigest()

def stream_hash(stream):
    h = hashlib.sha256()
    size = 0
    for block in iter(lambda: stream.read(1024 * 1024), b''):
        h.update(block)
        size += len(block)
    return size, h.hexdigest()

archives = read(HERE / 'data/large-artifact-archives.json')
assert archives['status'] == 'LOSSLESS_ARCHIVES_VERIFIED_ORIGINALS_RETAINED'
originals = {r['original'] for r in archives['files']}
for row in archives['files']:
    packed, raw = HERE / row['archive'], HERE / row['original']
    assert packed.is_relative_to(HERE) and raw.is_relative_to(HERE)
    with packed.open('rb') as f:
        assert stream_hash(f) == (row['archive_bytes'], row['archive_sha256']), str(packed)
    with gzip.open(packed, 'rb') as f:
        assert stream_hash(f) == (row['bytes'], row['sha256']), str(packed)
    if '--restore-archives' in sys.argv and not raw.exists():
        raw.parent.mkdir(parents=True, exist_ok=True)
        with gzip.open(packed, 'rb') as src, raw.open('xb') as dst:
            shutil.copyfileobj(src, dst, 1024 * 1024)
    if raw.exists():
        with raw.open('rb') as f:
            assert stream_hash(f) == (row['bytes'], row['sha256']), str(raw)
if '--restore-archives' in sys.argv:
    print('PASS_ARCHIVES_RESTORED_OR_ALREADY_PRESENT', len(archives['files']))
    sys.exit(0)

c = read(HERE / 'data/checkpoint.json')
manifest = HERE / 'data/file-manifest.json'
assert c['status'] == 'PASS_THREE_COUNT_RESTRICTION_AND_CONDITIONAL_FAMILY_TEST'
assert sha((ROOT / c['prior_checkpoint']).read_bytes()) == c['prior_checkpoint_sha256']
for p, key in [('data/proof-summary.json', 'proof_summary_sha256'), ('data/batch-observation.json', 'batch_observation_sha256'),
    ('audit/final-review.md', 'final_review_sha256'), ('mathematical-note.md', 'mathematical_note_sha256'),
    ('data/family-profiles/results.json', 'family_result_sha256'), ('data/combined-experiment.json', 'combined_result_sha256'),
    ('data/large-artifact-archives.json', 'archives_sha256')]:
    assert sha((HERE / p).read_bytes()) == c[key], p
pins = re.findall(r'^\| `([^`]+)` \| `([0-9a-f]{64})` \|$', (HERE / 'audit/final-review.md').read_text(encoding='utf-8'), re.M)
assert len(pins) == 17
for path, digest in pins:
    p = HERE / path
    if p.exists():
        assert sha(p.read_bytes()) == digest, path
    else:
        assert any(r['original'] == path and r['sha256'] == digest for r in archives['files']), path
assert not (HERE / 'data/check.lock').exists()
paper = (ROOT / 'paper/snake9_research.tex').read_bytes()
assert sha(paper) == c['paper_sha256']
editor = Path('D:/Codex/2026-10-13/new-chat/outputs/snake9_research.tex')
if editor.exists():
    assert paper == editor.read_bytes()
if '--verify' not in sys.argv and '--staged' not in sys.argv:
    assert not manifest.exists()
    paths = [p for p in HERE.rglob('*') if p.is_file() and p != manifest
        and not {'build', 'build-isolated', '__pycache__'} & set(p.relative_to(HERE).parts)
        and p.relative_to(HERE).as_posix() not in originals]
    paths += [ROOT / p for p in read(HERE / 'data/additional-batch-evidence.json')]
    paths += [ROOT / p for p in ['README.md', 'COLLABORATION.md', 'RESEARCH_LEDGER.md', 'milestones/README.md',
        'handoff/README.md', 'handoff/CURRENT_STATUS.md', 'handoff/NEXT_AGENT_PROMPT.md']]
    rows = [dict(path=p.relative_to(ROOT).as_posix(), bytes=p.stat().st_size, sha256=sha(p.read_bytes())) for p in sorted(set(paths))]
    assert all(r['bytes'] < 100 * 1024 * 1024 for r in rows), 'Unarchived file exceeds GitHub limit'
    manifest.write_text(json.dumps(dict(status='SAVED_CHECKED_THREE_COUNT_RESTRICTION_AND_CONDITIONAL_FAMILY', files=rows,
        raw_artifact_policy='Seven large originals retained locally and represented by lossless verified gzip archives.',
        scope='Checked actual-snake theorem, exact native conditional graph calculations, pending sum proofs, failed attempts, immutable batch observation and independent review. No improved integer snake bound.'), indent=2) + '\n', encoding='utf-8')
    print('SAVED_MANIFEST', len(rows), 'files', sum(r['bytes'] for r in rows), 'bytes')
else:
    rows = read(manifest)['files']
    for r in rows:
        raw = (ROOT / r['path']).read_bytes()
        assert len(raw) == r['bytes'] and sha(raw) == r['sha256'], r['path']
    if '--staged' in sys.argv:
        names = [r['path'] for r in rows] + [manifest.relative_to(ROOT).as_posix()]
        actual = subprocess.check_output(['git', '-c', 'core.commitGraph=false', 'diff', '--cached', '--name-only'], cwd=ROOT, text=True).splitlines()
        assert set(actual) == set(names), 'Index differs from reviewed manifest'
        index = ''.join(subprocess.check_output(['git', '-c', 'core.commitGraph=false', 'ls-files', '-s', '--', *names[i:i + 35]],
            cwd=ROOT, text=True) for i in range(0, len(names), 35))
        blobs = {line.split('\t', 1)[1]: line.split()[1] for line in index.splitlines()}
        for name in names:
            raw = (ROOT / name).read_bytes()
            if not name.startswith(('milestones/104-', 'milestones/111-')):
                raw = raw.replace(b'\r\n', b'\n')
            assert hashlib.sha1(b'blob ' + str(len(raw)).encode() + b'\0' + raw).hexdigest() == blobs[name], name
    print('PASS_EXACT_STAGED_FILES' if '--staged' in sys.argv else 'PASS_LOCAL_MANIFEST', len(rows))
