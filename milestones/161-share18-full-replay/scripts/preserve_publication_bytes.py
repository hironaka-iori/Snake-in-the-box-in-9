"""Preserve an unpublished manifest and restage exact bytes under -text."""
from pathlib import Path
import hashlib
import json
import subprocess

H = Path(__file__).resolve().parents[1]
R = H.parents[1]
G = ['git', '-c', 'core.commitGraph=false', '-c', 'maintenance.auto=false',
     '-c', 'gc.auto=0', '-c', 'core.autocrlf=false']

def git(*args):
    return subprocess.check_output(G + list(args), cwd=R)

def sha(b):
    return hashlib.sha256(b).hexdigest()

def main():
    p = H / 'data/publication-manifest.json'
    original = p.read_bytes()
    q = json.loads(original)
    data = q['files']
    for rel, item in data.items():
        assert sha((R / rel).read_bytes()) == item['sha256'], rel
    staged = set(git('diff', '--cached', '--name-only', '-z').decode().split('\0')) - {''}
    assert staged <= set(data) | {p.relative_to(R).as_posix()}
    backup = H / 'data/publication-manifest-before-attributes.json'
    assert not backup.exists()
    backup.write_bytes(original)
    attributes = H / '.gitattributes'
    assert attributes.read_text().strip() == '* -text'
    for added in [backup, attributes, Path(__file__)]:
        data[added.relative_to(R).as_posix()] = dict(sha256=sha(added.read_bytes()), bytes=added.stat().st_size)
    q['publication_note'] = 'The initial unpublished manifest omitted the milestone -text attribute. Preserve its bytes and restage under -text before exact-index verification. No accepted proof artifact was changed.'
    p.write_text(json.dumps(q, indent=2) + '\n', encoding='utf-8')
    paths = list(data) + [p.relative_to(R).as_posix()]
    for start in range(0, len(paths), 50):
        git('add', '-f', '--', *paths[start:start+50])
        git('add', '--renormalize', '--', *paths[start:start+50])
    expected = {rel: row['sha256'] for rel, row in data.items()}
    expected[p.relative_to(R).as_posix()] = sha(p.read_bytes())
    staged = set(git('diff', '--cached', '--name-only', '-z').decode().split('\0')) - {''}
    assert staged <= set(expected)
    raw = git('ls-files', '--stage', '-z', '--', H.relative_to(R).as_posix(),
              'README.md', 'handoff/CURRENT_STATUS.md', 'handoff/NEXT_AGENT_PROMPT.md', 'paper/snake9_research.tex')
    index = {}
    for item in raw.split(b'\0'):
        if not item:
            continue
        metadata, name = item.split(b'\t', 1)
        _, oid, stage = metadata.split()
        assert stage == b'0'
        index[name.decode()] = oid
    child = subprocess.Popen(G + ['cat-file', '--batch'], cwd=R,
                             stdin=subprocess.PIPE, stdout=subprocess.PIPE)
    try:
        for rel, digest in expected.items():
            child.stdin.write(index[rel] + b'\n')
            child.stdin.flush()
            oid, kind, size = child.stdout.readline().split()
            assert oid == index[rel] and kind == b'blob'
            remaining = int(size)
            h = hashlib.sha256()
            while remaining:
                block = child.stdout.read(min(1048576, remaining))
                assert block
                h.update(block)
                remaining -= len(block)
            assert child.stdout.read(1) == b'\n'
            assert h.hexdigest() == digest, rel
        child.stdin.close()
        assert child.wait(timeout=30) == 0
    finally:
        if child.poll() is None:
            child.terminate()
            child.wait(timeout=30)
    print('PASS_EXACT_INDEX_BYTES', len(expected), 'files;', len(staged), 'changed paths.')

if __name__ == '__main__':
    main()
