"""Archive a partial case without issuing a completed-theorem receipt."""
from pathlib import Path
import gzip
import hashlib
import json
import re
import shutil
import sys
import tarfile

TASK = Path(__file__).resolve().parents[1]
ROOT = TASK.parents[1]
HERE = ROOT / 'milestones/73-countfree-share-catalogue'
assert sys.argv[1:] in [['7302'], ['7302', '--verify']]
OUT = HERE / 'cases/case7302'
read = lambda p: json.loads(p.read_text())


def sha(p):
    h = hashlib.sha256()
    with p.open('rb') as stream:
        for chunk in iter(lambda: stream.read(1024*1024), b''):
            h.update(chunk)
    return h.hexdigest()


def pack(destination, files, base):
    with destination.open('wb') as raw:
        with gzip.GzipFile(fileobj=raw, mode='wb', compresslevel=6, mtime=0) as gz:
            with tarfile.open(fileobj=gz, mode='w|') as tf:
                for p in files:
                    info = tarfile.TarInfo(p.relative_to(base).as_posix())
                    info.size = p.stat().st_size
                    info.mode = 0o644
                    info.mtime = 0
                    with p.open('rb') as stream:
                        tf.addfile(info, stream)


def check_archive(path, expected):
    found = {}
    with tarfile.open(path, 'r:gz') as tf:
        for member in tf:
            assert member.isfile() and member.name not in found
            assert not Path(member.name).is_absolute() and '..' not in Path(member.name).parts
            h = hashlib.sha256()
            stream = tf.extractfile(member)
            for chunk in iter(lambda: stream.read(1024*1024), b''):
                h.update(chunk)
            found[member.name] = h.hexdigest()
    assert found == expected


if '--verify' in sys.argv:
    saved = read(OUT / 'data/pending-checkpoint.json')
    assert saved['status'] == 'SEMANTICS_CHECKED_REFUTATION_REPLAY_PENDING'
    for item in saved['archives']:
        path = OUT / item['path']
        assert sha(path) == item['sha256']
        check_archive(path, item['members'])
        for part in item.get('parts', []):
            assert sha(OUT / part['path']) == part['sha256']
    for rel, digest in saved['source_sha256'].items():
        assert sha(OUT / rel) == digest
    for item in saved['compiled_modules']:
        assert sha(OUT / item['source']) == item['source_sha256']
        assert sha(OUT / item['object']) == item['object_sha256']
        assert sha(OUT / item['log']) == item['log_sha256']
    for rel, digest in saved['receipts'].items():
        assert sha(OUT / rel) == digest
    print('PASS_PENDING_ARCHIVE_AND_LOCAL_EVIDENCE', len(saved['source_sha256']), 'sources')
    raise SystemExit(0)

assert not (OUT / 'data/proof-audit.json').exists(), 'Use completed-case archive for a finished theorem'
selection = read(OUT / 'data/lrat-slice-selection.json')
assert selection['status'] == 'SLICED_LRAT_SELECTED_AND_RESIMULATED'
assert sha(OUT / 'certificates/share7302.cnf') == selection['input_cnf_sha256']
assert sha(OUT / 'certificates/share7302.lrat') == selection['selected_lrat_sha256']
assert sha(OUT / 'data/export.json') == selection['export_receipt_sha256']
assert sha(OUT / 'data/lrat-generation.json') == selection['generation_receipt_sha256']
assert read(OUT / 'data/export.json')['simulated']
sources = sorted((OUT / 'lean').rglob('*.lean'))
for source in sources:
    assert not re.search(r'\b(sorry|admit|native_decide)\b', source.read_text())
source_hashes = {p.relative_to(OUT).as_posix(): sha(p) for p in sources}
compiled = []
receipts = {}
for name in ['semantic-record.json', 'composition-record.json']:
    path = OUT / 'logs' / name
    record = read(path)
    receipts[path.relative_to(OUT).as_posix()] = sha(path)
    for row in record['records']:
        module = row['module']
        source = OUT / 'lean' / (module + '.lean')
        obj = Path(record['build']) / (module + '.olean')
        log = OUT / 'logs' / (module.replace('/', '-') + '.log')
        assert row['exit_code'] == 0 and sha(source) == row['source_sha256']
        for dep, digest in row.get('dependencies', {}).items():
            assert sha(OUT / 'lean' / (dep + '.lean')) == digest
        text = log.read_text()
        assert all(bad not in text for bad in ['error:', 'sorryAx', 'failed to delete'])
        axioms = re.findall(r"'([^']+)' depends on axioms:\s*\[([^]]*)\]", text, re.S)
        for _, values in axioms:
            assert set(re.findall(r'[A-Za-z][\w.]*', values)) <= {'propext','Classical.choice','Quot.sound'}
        compiled.append(dict(module=module, source=source.relative_to(OUT).as_posix(),
                             source_sha256=sha(source), object=obj.relative_to(OUT).as_posix(),
                             object_sha256=sha(obj), log=log.relative_to(OUT).as_posix(),
                             log_sha256=sha(log), theorem_audits=axioms))
assert sum(r['module'].startswith('Share7302/Shard') for r in compiled) == 121
assert {'Share7302/Compose', 'Share7302/Sat'} <= {r['module'] for r in compiled}
assert not any(r['module'].startswith('LocalWindowUnsat') for r in compiled)

archives = []
groups = [('data/pending-lean-sources.tar.gz', sources, OUT)]
backup = (OUT / selection['backup_manifest']).parent
original = sorted(p for p in (backup / 'original').rglob('*') if p.is_file())
original.append(backup / 'original-lean-manifest.json')
groups.append(('data/original-proof-evidence.tar.gz', original, backup))
groups.append(('data/pending-compact-proof.tar.gz',
               [OUT/'certificates/share7302.cnf', OUT/'certificates/share7302.lrat'], OUT))
for relative, files, base in groups:
    destination = OUT / relative
    pack(destination, files, base)
    members = {p.relative_to(base).as_posix(): sha(p) for p in files}
    check_archive(destination, members)
    archives.append(dict(path=relative, bytes=destination.stat().st_size,
                         sha256=sha(destination), members=members))
for path in sorted((OUT / 'data').glob('*.json')):
    if path.name != 'pending-checkpoint.json':
        receipts[path.relative_to(OUT).as_posix()] = sha(path)
saved = dict(status='SEMANTICS_CHECKED_REFUTATION_REPLAY_PENDING', case_number=7302,
             target_share=20, pattern='012034', compiled_modules=compiled,
             source_sha256=source_hashes, archives=archives, receipts=receipts,
             selected_lrat_sha256=selection['selected_lrat_sha256'],
             remaining=['Lean replay of selected LRAT and checker soundness',
                        'Compile final geometric and reversal theorem wrappers',
                        'Run complete case source, encoding and axiom audit',
                        'Integrate only after completed audit passes'],
             scope='Partial proof preservation. Semantic clauses and composition were checked against reused support. No completed local refutation or new global bound. Build caches remain local and are not included in source/proof archives.')
(OUT / 'data/pending-checkpoint.json').write_text(json.dumps(saved, indent=2)+'\n')
print(saved['status'], len(compiled), 'checked modules;', len(sources), 'saved sources;',
      sum(a['bytes'] for a in archives), 'archived bytes', flush=True)
import runpy
runpy.run_path(str(TASK / 'scripts/split_archives.py'))
