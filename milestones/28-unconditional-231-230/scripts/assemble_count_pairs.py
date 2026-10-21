"""Retain verified count proofs and audit their isolated two-centre assembly.

Only completed, source/dependency/artifact-matching donor modules are reused.
This is incremental evidence, never a substitute for the final fresh build.
"""
import argparse
import json
from pathlib import Path
import shutil
import develop_lean as dev
import runner as r

JOB = r.HERE / 'runtime/count-pair-assembly'
DEST = r.HERE / 'lean'
TARGET = 'CountWindowPairs231Assembly'
PREFIXES = ['FastCountD012A11', 'FastCountD012A12', 'FastCountD012A13', 'FastCountQ012A14']
ROOTS = [name + '.LocalWindow' for name in PREFIXES]
DONOR = r.HERE / 'runtime/bridge-development'


def readiness():
    state = r.read(DONOR / 'state.json')
    missing = [name for name in ROOTS if name not in state.get('completed', {})]
    return dict(status='waiting_for_refutations' if missing else 'ready_for_hash_validation',
                missing=missing, target=TARGET, global_231='UNRESOLVED')


def assemble():
    import msvcrt
    JOB.mkdir(parents=True, exist_ok=True)
    held = (JOB / 'worker.lock').open('a+b')
    held.seek(0); held.write(b'0'); held.flush(); held.seek(0)
    msvcrt.locking(held.fileno(), msvcrt.LK_NBLCK, 1)
    try:
        ready = readiness()
        assert not ready['missing'], ('Refutations still incomplete', ready['missing'])
        original = r.read(r.HERE / 'runtime/manifest.json'); r.validate(original)
        cfg = original['config']
        donors = []
        for folder in ['bridge-development', 'count-pair-bridge']:
            base = r.HERE / 'runtime' / folder
            snapshot = JOB / 'donors' / (folder + '.json')
            state = r.read(base / 'state.json'); r.atomic(snapshot, state)
            donors.append((base, {**state.get('base_dependencies', {}), **state['completed']}, r.digest(snapshot)))
        count_rows = donors[0][1]
        for name in ROOTS:
            row = count_rows[name]
            audits = row.get('axioms', row.get('axiom_audits', []))
            assert len(audits) == 2, ('Missing count audits', name)
            assert all(set(a['axioms']) <= r.ALLOWED for a in audits), ('Disallowed axioms', name)
        exported, visited = {}, set()

        def export(name):
            if name in visited or not any(name.startswith(prefix + '.') for prefix in PREFIXES):
                return
            visited.add(name)
            row = count_rows[name]
            relative = name.replace('.', '/') + '.lean'
            source = DONOR / 'src' / relative
            assert r.digest(source) == row['source_sha256']
            assert r.digest(source.with_suffix('.olean')) == row['artifact_sha256']
            for dep in row['dependency_hashes']:
                export(dep)
            data = source.read_bytes().replace(b'\r\n', b'\n')
            dest = DEST / relative; dest.parent.mkdir(parents=True, exist_ok=True)
            if dest.exists():
                assert dest.read_bytes().replace(b'\r\n', b'\n') == data, ('Existing proof source differs', relative)
            else:
                dest.write_bytes(data)
            exported[relative] = r.digest(dest)

        for name in ROOTS:
            export(name)
        dev.BUILD = JOB; dev.SOURCE = JOB / 'src'; dev.SOURCE.mkdir(parents=True, exist_ok=True)
        receipt = JOB / 'state.json'
        state = r.read(receipt) if receipt.exists() else dict(completed={})
        checked, seeded = {}, {}

        def seed(name):
            if name.startswith(('Init', 'Lean', 'Std', 'Mathlib')):
                return None
            if name in checked:
                return checked[name]
            relative = name.replace('.', '/') + '.lean'
            source = next((r.ROOT/folder/relative for folder in dev.SEARCH
                           if (r.ROOT/folder/relative).exists()), None)
            assert source, ('Missing assembly dependency', name)
            data = source.read_text(encoding='utf-8').replace('\r\n', '\n').encode()
            deps = {}
            for line in data.decode().splitlines():
                if line.startswith('import '):
                    for dep in line.split('--')[0].split()[1:]:
                        value = seed(dep)
                        if value:
                            deps[dep] = value
            sha = r.hashbytes(data)
            fingerprint = r.hashbytes(json.dumps([sha, deps, cfg['lean_version'], cfg['tools'],
                                                  cfg['mathlib_commit']], sort_keys=True).encode())
            for base, rows, snapshot in donors:
                row = rows.get(name)
                if not row or row['closure_hash'] != fingerprint:
                    continue
                src = base / 'src' / relative
                assert r.digest(src) == sha
                assert r.digest(src.with_suffix('.olean')) == row['artifact_sha256']
                dest = dev.SOURCE / relative; dest.parent.mkdir(parents=True, exist_ok=True)
                dest.write_bytes(data); shutil.copyfile(src.with_suffix('.olean'), dest.with_suffix('.olean'))
                state['completed'][name] = dict(row, axioms=row.get('axioms', row.get('axiom_audits', [])),
                                               donor=str(base), donor_snapshot_sha256=snapshot)
                seeded[name] = str(base)
                break
            assert name == TARGET or name in seeded, ('Dependency not fully validated; do not rebuild it concurrently', name)
            checked[name] = fingerprint
            return fingerprint

        seed(TARGET)
        state.update(reuse_scope='Source, dependency and artifact validated; not a fresh rebuild',
                     assembly_script_sha256=r.digest(__file__))
        r.atomic(receipt, state)
        r.atomic(r.HERE/'data/count-pair-assembly-input.json', dict(
            target=TARGET, roots=ROOTS, source_commit=r.git('rev-parse', 'HEAD').decode().strip(),
            exported_files=exported, reused_modules=seeded, script_sha256=r.digest(__file__),
            root_source_sha256=r.digest(DEST/(TARGET+'.lean')),
            scope='Verified components retained; new assembly root still requires compilation and audit'))
        print('Exported', len(exported), 'sources; validated dependencies:', len(seeded), flush=True)
        dev.main([TARGET])
        completed = r.read(receipt)
        audits = completed['completed'][TARGET]['axioms']
        assert len(audits) == 2 and all(set(a['axioms']) <= r.ALLOWED for a in audits)
        r.atomic(r.HERE/'data/count-pair-assembly-development.json', completed)
    finally:
        held.close()


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('--check-ready', action='store_true', help='Report missing roots without compiling or exporting')
    args = parser.parse_args()
    print(json.dumps(readiness())) if args.check_ready else assemble()
