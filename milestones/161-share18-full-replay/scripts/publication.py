"""Manifest-scoped staging and exact byte verification for milestone161."""
import argparse
import hashlib
import json
from pathlib import Path
import subprocess

ROOT = Path(__file__).resolve().parents[3]
HERE = Path(__file__).resolve().parents[1]
MANIFEST = HERE / 'data/publication-manifest.json'
GIT = ['git', '-c', 'core.commitGraph=false', '-c', 'maintenance.auto=false',
       '-c', 'gc.auto=0', '-c', 'core.autocrlf=false']

def sha(raw):
    return hashlib.sha256(raw).hexdigest()

def git(*args):
    return subprocess.check_output(GIT + list(args), cwd=ROOT)

def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('mode', choices=['create', 'stage', 'verify'])
    args = parser.parse_args()
    if args.mode == 'create':
        assert not MANIFEST.exists(), 'Preserve published manifests.'
        assert not git('diff', '--cached', '--name-only').strip(), 'Index contains other work.'
        files = [p for p in HERE.rglob('*') if p.is_file() and '__pycache__' not in p.parts and 'source-columns' not in p.parts]
        files += [ROOT / name for name in ['README.md', 'handoff/CURRENT_STATUS.md',
                  'handoff/NEXT_AGENT_PROMPT.md', 'paper/snake9_research.tex']]
        data = {p.relative_to(ROOT).as_posix(): {'sha256': sha(p.read_bytes()), 'bytes': p.stat().st_size}
                for p in sorted(files)}
        MANIFEST.write_text(json.dumps({'files': data, 'scope': 'Milestone161 and four current documents only.'}, indent=2) + '\n', encoding='utf-8')
        print('Created manifest for', len(data), 'files.')
        return
    data = json.loads(MANIFEST.read_text(encoding='utf-8'))['files']
    for rel, item in data.items():
        assert sha((ROOT / rel).read_bytes()) == item['sha256'], rel
    data[MANIFEST.relative_to(ROOT).as_posix()] = {'sha256': sha(MANIFEST.read_bytes())}
    if args.mode == 'stage':
        assert not git('diff', '--cached', '--name-only').strip(), 'Index contains other work.'
        for start in range(0, len(data), 50):
            git('add', '-f', '--', *list(data)[start:start+50])
    staged = set(git('diff', '--cached', '--name-only', '-z').decode('utf-8').split('\0')) - {''}
    assert staged <= set(data), sorted(staged - set(data))
    for rel, item in data.items():
        assert sha(git('show', ':' + rel)) == item['sha256'], rel
    print('PASS_EXACT_INDEX_BYTES', len(data), 'files;', len(staged), 'changed paths.')

if __name__ == '__main__':
    main()
