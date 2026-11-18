"""Create, stage and verify an exact-byte, narrowly scoped publication manifest.

No commit or push operation is provided. The manifest excludes itself to avoid
a circular hash; stage/verify add its current exact bytes to the expected index.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path, PurePosixPath
import stat
import subprocess

ROOT = Path(__file__).resolve().parents[3]
HERE = Path(__file__).resolve().parents[1]
PREVIOUS = HERE
MANIFEST = HERE / 'data/publication-manifest.json'
SCOPES = [PREVIOUS.relative_to(ROOT).as_posix(), HERE.relative_to(ROOT).as_posix()]
DOCUMENTS = ['README.md','handoff/CURRENT_STATUS.md','handoff/NEXT_AGENT_PROMPT.md','paper/snake9_research.tex','paper/snake9_frontier_explanation.tex']
GIT = ['git', '-c', 'core.commitGraph=false', '-c', 'maintenance.auto=false',
       '-c', 'gc.auto=0', '-c', 'core.autocrlf=false']
CACHE_DIRS = {'source-columns', 'journal', '__pycache__', '.pytest_cache', '.mypy_cache', '.ruff_cache',
              '.cache', 'cache', 'tmp', 'temp'}
BLOCK = 1024 * 1024


def require(condition, message):
    if not condition:
        raise RuntimeError(message)


def git(*args, input_bytes=None):
    return subprocess.run(GIT + list(args), cwd=ROOT, input=input_bytes,
                          stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                          check=True).stdout


def names(raw):
    return [x.decode('utf-8') for x in raw.split(b'\0') if x]


def relative(path):
    return path.relative_to(ROOT).as_posix()


def excluded(rel):
    parts = PurePosixPath(rel).parts
    name = parts[-1].lower()
    return (any(x.lower() in CACHE_DIRS for x in parts)
            or name.endswith(('.tmp', '.temp', '.lock', '.pyc', '.pyo', '.pbtxt', '~'))
            or '.tmp.' in name or '.lock.' in name)


def permitted(rel):
    p = PurePosixPath(rel)
    return (not p.is_absolute() and '..' not in p.parts and '\\' not in rel
            and (rel in DOCUMENTS or any(rel.startswith(s + '/') for s in SCOPES)))


def file_path(rel):
    require(permitted(rel), 'Path outside publication scope: ' + rel)
    p = ROOT / rel
    require(p.resolve().is_relative_to(ROOT.resolve()), 'Path escapes repository: ' + rel)
    require(not p.is_symlink(), 'Symlink is unsupported: ' + rel)
    return p


def fingerprint(path):
    before = path.stat()
    require(stat.S_ISREG(before.st_mode), 'Expected regular file: ' + str(path))
    digest = hashlib.sha256()
    count = 0
    with path.open('rb') as stream:
        for block in iter(lambda: stream.read(BLOCK), b''):
            digest.update(block)
            count += len(block)
    after = path.stat()
    require((before.st_size, before.st_mtime_ns) == (after.st_size, after.st_mtime_ns)
            and count == after.st_size, 'File changed during hashing: ' + str(path))
    return {'sha256': digest.hexdigest(), 'bytes': count}


def empty_index():
    require(not git('diff', '--cached', '--name-only', '-z', '--no-renames'),
            'Index contains other work; an empty index is required.')
    require(not git('ls-files', '--unmerged', '-z'), 'Index contains unresolved entries.')


def stopped():
    for path in [ROOT / 'work/fullgraph-active.lock', PREVIOUS / 'data/replay-batch.lock',
                 PREVIOUS / 'data/preparation-worker.lock',
                 HERE / 'data/replay-batch.lock', HERE / 'data/history-search.lock',
                 HERE / 'data/forest-search.lock']:
        require(not path.exists(), 'Active publication input: ' + relative(path))


def filesystem_files(folder):
    # Only the two milestone directories are traversed; ignored files are kept.
    for directory, dirs, files in os.walk(folder, followlinks=False):
        base = Path(directory)
        keep = []
        for name in dirs:
            path = base / name
            if name.lower() in CACHE_DIRS or name.lower().startswith('journal-floor'):
                continue
            require(not path.is_symlink() and not path.is_junction(),
                    'Directory link is unsupported: ' + relative(path))
            keep.append(name)
        dirs[:] = keep
        for name in files:
            path = base / name
            rel = relative(path)
            if path == MANIFEST or excluded(rel):
                continue
            file_path(rel)
            yield rel


def selection():
    tracked = set(names(git('ls-files', '-z', '--', SCOPES[0])))
    baseline = set(names(git('ls-tree', '-r', '--name-only', '-z', 'HEAD', '--', SCOPES[0])))
    changed = set(names(git('diff', 'HEAD', '--name-only', '-z', '--no-renames',
                            '--', SCOPES[0])))
    require(changed <= (tracked | baseline), 'Unexpected nontracked diff entries.')
    historical = {p for p in changed & baseline if 'manifest' in PurePosixPath(p).name.lower()}
    require(not historical, 'Preserve historical manifests: ' + repr(sorted(historical)))
    previous_files = set(filesystem_files(PREVIOUS))
    selected = set(filesystem_files(HERE)) | (previous_files - tracked)
    selected |= {p for p in changed if not excluded(p)}
    selected |= set(DOCUMENTS)
    selected.discard(relative(MANIFEST))
    result = {}
    for rel in sorted(selected):
        path = file_path(rel)
        if path.exists():
            result[rel] = {'action': 'add', **fingerprint(path)}
        else:
            require(rel in changed and rel in baseline,
                    'Required publication file is absent: ' + rel)
            result[rel] = {'action': 'delete'}
    require(relative(Path(__file__)) in result, 'Publication helper is not manifested.')
    return result


def load_manifest():
    raw = MANIFEST.read_bytes()
    data = json.loads(raw)
    require(data.get('version') == 1, 'Unsupported publication manifest.')
    require(data['base_head'] == git('rev-parse', 'HEAD').decode('ascii').strip(),
            'HEAD changed after manifest creation.')
    require(data['scopes'] == SCOPES and data['documents'] == DOCUMENTS,
            'Unexpected manifest scope.')
    require(relative(MANIFEST) not in data['files'], 'Manifest must not hash itself.')
    require(selection() == data['files'],
            'Publication files changed or appeared after manifest creation.')
    return data, raw


def index_entries():
    entries = {}
    for record in git('ls-files', '--stage', '-z', '--', *SCOPES, *DOCUMENTS).split(b'\0'):
        if not record:
            continue
        header, raw_path = record.split(b'\t', 1)
        mode, oid, stage = header.decode('ascii').split()
        rel = raw_path.decode('utf-8')
        require(stage == '0' and rel not in entries, 'Unmerged or duplicate index path: ' + rel)
        entries[rel] = (mode, oid)
    return entries


def verify_index(data, manifest_raw):
    expected = dict(data['files'])
    expected[relative(MANIFEST)] = {'action': 'add', 'bytes': len(manifest_raw),
                                  'sha256': hashlib.sha256(manifest_raw).hexdigest()}
    changed = set(names(git('diff', '--cached', '--name-only', '-z', '--no-renames')))
    require(changed <= set(expected), 'Unmanifested staged paths: ' + repr(sorted(changed - set(expected))))
    entries = index_entries()
    process = subprocess.Popen(GIT + ['cat-file', '--batch'], cwd=ROOT,
                               stdin=subprocess.PIPE, stdout=subprocess.PIPE,
                               stderr=subprocess.PIPE)
    try:
        for rel, item in sorted(expected.items()):
            if item['action'] == 'delete':
                require(rel not in entries and rel in changed, 'Deletion not staged: ' + rel)
                continue
            require(rel in entries, 'Manifest file missing from index: ' + rel)
            mode, oid = entries[rel]
            require(mode in {'100644', '100755'}, 'Unsupported index mode: ' + rel)
            process.stdin.write((oid + '\n').encode('ascii'))
            process.stdin.flush()
            header = process.stdout.readline().decode('ascii').rstrip('\n').split()
            require(len(header) == 3 and header[0] == oid and header[1] == 'blob',
                    'Invalid batch object response: ' + rel)
            size = int(header[2])
            require(size == item['bytes'], 'Index byte length differs: ' + rel)
            digest = hashlib.sha256()
            remaining = size
            while remaining:
                chunk = process.stdout.read(min(BLOCK, remaining))
                require(bool(chunk), 'Truncated index blob: ' + rel)
                digest.update(chunk)
                remaining -= len(chunk)
            require(process.stdout.read(1) == b'\n', 'Invalid batch blob terminator: ' + rel)
            require(digest.hexdigest() == item['sha256'], 'Index bytes differ: ' + rel)
        process.stdin.close()
        require(process.wait(timeout=30) == 0, 'git cat-file failed.')
        require(not process.stderr.read(), 'Unexpected git cat-file diagnostics.')
    finally:
        if process.poll() is None:
            process.kill()
            process.wait()
        for stream in [process.stdin, process.stdout, process.stderr]:
            if not stream.closed:
                stream.close()
    require(index_entries() == entries, 'Index changed during verification.')
    require(set(names(git('diff', '--cached', '--name-only', '-z', '--no-renames'))) == changed,
            'Staged path set changed during verification.')
    require(MANIFEST.read_bytes() == manifest_raw, 'Manifest changed during verification.')
    stopped()
    print('PASS_EXACT_INDEX_BYTES', len(expected), 'manifest paths;', len(changed), 'changed paths.')


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('mode', choices=['create', 'stage', 'verify'])
    args = parser.parse_args()
    stopped()
    if args.mode in {'create', 'stage'}:
        empty_index()
    if args.mode == 'create':
        require(not MANIFEST.exists(), 'Preserve existing publication manifest.')
        base_head = git('rev-parse', 'HEAD').decode('ascii').strip()
        files = selection()
        require(git('rev-parse', 'HEAD').decode('ascii').strip() == base_head,
                'HEAD changed while preparing manifest.')
        empty_index()
        stopped()
        data = {'version': 1, 'base_head': base_head, 'scopes': SCOPES,
                'documents': DOCUMENTS, 'files': files,
                'self_policy': 'Manifest excluded from its own files; its exact bytes are separately verified in the index.',
                'scope': 'Round237 research artifacts and current documents; exact-byte publication.'}
        MANIFEST.parent.mkdir(parents=True, exist_ok=True)
        with MANIFEST.open('xb') as stream:
            stream.write((json.dumps(data, indent=2) + '\n').encode('utf-8'))
        print('CREATED_PUBLICATION_MANIFEST', len(files), 'files')
        return
    data, raw = load_manifest()
    if args.mode == 'stage':
        empty_index()
        # Literal NUL-delimited pathspecs avoid Windows command-length limits.
        paths = sorted(set(data['files']) | {relative(MANIFEST)})
        pathspec = b''.join((':(literal)' + p).encode('utf-8') + b'\0' for p in paths)
        git('add', '-f', '--pathspec-from-file=-', '--pathspec-file-nul', input_bytes=pathspec)
        # This milestone preserves bytes with its own -text attribute. The batch
        # verification below compares every staged blob with the exact manifest;
        # any mismatch stops publication before committing.
        require(MANIFEST.read_bytes() == raw, 'Manifest changed during staging.')
        # Selection uses HEAD rather than the staged state, so it remains valid.
        require(selection() == data['files'], 'Inputs changed during staging.')
    verify_index(data, raw)


if __name__ == '__main__':
    main()
