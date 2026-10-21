"""Join completed exact-CNF Boolean and geometric proofs without rerunning them.

Generated proof sources are retained in the research tree. The isolated build
reuses only matching source/dependency/artifact hashes, then audits the new root.
This remains incremental development evidence, not the final fresh global build.
"""
import argparse
import json
from pathlib import Path
import shutil
import develop_lean as dev
import runner as r

JOB = r.HERE / 'runtime/share-assembly'
DEST = r.HERE / 'lean'


def assemble(index):
    assert index in range(34) and index != 1, 'Case 01 already has its complete canonical theorem'
    import msvcrt
    JOB.mkdir(parents=True, exist_ok=True)
    held = (JOB / 'worker.lock').open('a+b')
    held.seek(0); held.write(b'0'); held.flush(); held.seek(0)
    msvcrt.locking(held.fileno(), msvcrt.LK_NBLCK, 1)
    try:
        app = r.HERE / 'runtime/applicability'
        app_state = r.read(app / 'state.json')
        app_case = app_state['cases'][str(index)]
        case = r.read(app / 'cases' / f'{index:02d}.json')
        assert r.digest(app / 'cases' / f'{index:02d}.json') == app_case['generation_receipt_sha256']
        assert app_state['completed'][case['target']]['closure_hash'] == app_case['closure_hash']
        module = f'ParallelShare{index:02d}'
        fast = f'FastShare{index:02d}'
        boolean = r.HERE / ('runtime/bridge-development' if index == 0 else 'runtime/fast-kernel')
        boolean_state = r.read(boolean / 'state.json')
        boolean_target = fast + ('.LocalWindowV2' if index == 0 else '.LocalWindow')
        assert boolean_target in boolean_state['completed'], 'Boolean bridge is not completed'
        core = f'LocalWindowCnf/{module}.lean'
        assert r.digest(boolean / 'src' / core) == case['generated_files'][core]
        exported = {}
        def export(relative, source):
            data = source.read_bytes()
            dest = DEST / relative; dest.parent.mkdir(parents=True, exist_ok=True)
            if dest.exists():
                assert dest.read_bytes().replace(b'\r\n', b'\n') == data.replace(b'\r\n', b'\n'), ('Existing source differs', dest)
            else:
                dest.write_bytes(data)
            exported[relative] = r.digest(dest)
        for relative, digest in case['generated_files'].items():
            source = app / 'src' / relative
            assert r.digest(source) == digest
            export(relative, source)
        visited = set()
        def export_boolean(name):
            if name in visited or not name.startswith(fast + '.'):
                return
            visited.add(name)
            relative = name.replace('.', '/') + '.lean'
            source = boolean / 'src' / relative
            row = boolean_state['completed'][name]
            assert r.digest(source) == row['source_sha256']
            assert r.digest(source.with_suffix('.olean')) == row['artifact_sha256']
            for dep in row['dependency_hashes']:
                export_boolean(dep)
            export(relative, source)
        export_boolean(boolean_target)
        original = r.read(r.HERE / 'runtime/manifest.json'); r.validate(original)
        cfg = original['config']; directions = original['cases'][index]['dirs']
        target = f'LocalWindowSat.{module}CanonicalWindow'
        namespace = f'Snake9.LocalWindow.{module}CanonicalWindow'
        code = (f'import {boolean_target}\nimport {case["target"]}\nimport ParallelShareShapeBridge\n\n'
            + '/-! Completed Boolean and geometric proofs, on every matching canonical window. -/\n'
            + f'namespace {namespace}\nopen WindowAutomaton ParallelShareShapeBridge\n\n'
            + f'def directions : List Nat := {directions}\n\n'
            + 'theorem canonical_refuted :\n'
            + '    RefutedParallel (winOf directions) (List.replicate 6 (0, 21)) 20 :=\n'
            + f'  {module}Applicability.refuted_of_unsat Fast{module}.unsat\n\n'
            + 'theorem share_ge_21 {m : Nat} (p : Snake m) (r : Nat) (hr : r + 7 ≤ m)\n'
            + '    (hshape : canon (blockList p r 7) = directions) :\n'
            + '    21 ≤ ((List.range 6).map fun i => coreParallelShare p (r + i + 1)).sum := by\n'
            + '  apply refuted_canonical_window p r 7 20 (by decide) hr\n'
            + '  rw [hshape]\n  exact canonical_refuted\n\n'
            + '#print axioms canonical_refuted\n#print axioms share_ge_21\n'
            + f'end {namespace}\n')
        leaf = DEST / (target.replace('.', '/') + '.lean')
        if leaf.exists():
            assert leaf.read_text(encoding='utf-8') == code
        else:
            leaf.parent.mkdir(parents=True, exist_ok=True); leaf.write_text(code, encoding='utf-8', newline='\n')
        exported[leaf.relative_to(DEST).as_posix()] = r.digest(leaf)
        donors = []
        for folder in ['applicability', 'bridge-development', 'count-pair-bridge', 'fast-kernel']:
            base = r.HERE / 'runtime' / folder
            state = r.read(base / 'state.json')
            snapshot = JOB / 'donors' / f'{folder}-{index:02d}.json'
            r.atomic(snapshot, state)
            donors.append((base, {**state.get('base_dependencies', {}), **state['completed']}, r.digest(snapshot)))
        dev.BUILD = JOB; dev.SOURCE = JOB / 'src'; dev.SOURCE.mkdir(parents=True, exist_ok=True)
        receipt = JOB / 'state.json'
        state = r.read(receipt) if receipt.exists() else dict(completed={})
        seeded, checked = {}, {}
        def seed(name):
            if name.startswith(('Init', 'Lean', 'Std', 'Mathlib')):
                return None
            if name in checked:
                return checked[name]
            relative = name.replace('.', '/') + '.lean'
            source = next((r.ROOT/folder/relative for folder in dev.SEARCH if (r.ROOT/folder/relative).exists()), None)
            assert source, ('Missing source', name)
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
                assert r.digest(src) == sha and r.digest(src.with_suffix('.olean')) == row['artifact_sha256']
                dest = dev.SOURCE / relative; dest.parent.mkdir(parents=True, exist_ok=True); dest.write_bytes(data)
                shutil.copyfile(src.with_suffix('.olean'), dest.with_suffix('.olean'))
                state['completed'][name] = dict(row, axioms=row.get('axioms', row.get('axiom_audits', [])),
                                               donor=str(base), donor_snapshot_sha256=snapshot)
                seeded[name] = str(base)
                break
            checked[name] = fingerprint
            return fingerprint
        seed(target)
        state.update(reuse_scope='Source, dependency and artifact validated; not a fresh rebuild',
                     assembly_script_sha256=r.digest(__file__))
        r.atomic(receipt, state)
        r.atomic(r.HERE / 'data' / f'share-assembly-{index:02d}-input.json', dict(
            index=index, target=target, directions=directions, exported_files=exported,
            applicability_generation_sha256=r.digest(app / 'cases' / f'{index:02d}.json'),
            boolean_target=boolean_target, boolean_source_sha256=boolean_state['completed'][boolean_target]['source_sha256'],
            reused_modules=seeded, script_sha256=r.digest(__file__),
            scope='Completed-component source assembly; the new root must still compile and be audited'))
        print('Exported', len(exported), 'sources; validated reusable modules:', len(seeded), flush=True)
        dev.main([target])
    finally:
        held.close()


if __name__ == '__main__':
    parser = argparse.ArgumentParser(); parser.add_argument('--index', type=int, required=True)
    assemble(parser.parse_args().index)
