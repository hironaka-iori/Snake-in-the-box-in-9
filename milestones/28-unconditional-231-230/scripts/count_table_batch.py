"""Frozen, resumable kernel coverage checks for the four-to-six-centre tables.

Hash-validated dependency reuse is recorded explicitly. This is not the final
fresh global build, and local refutation families remain separate obligations.
"""
import argparse
import json
import os
from pathlib import Path
import shutil
import subprocess
import time
import traceback
import runner as r
from develop_lean import SEARCH

JOB = r.HERE / 'runtime/count-tables'
SRC = JOB / 'src'
DONOR = r.HERE / 'runtime/count-pair-bridge'
TARGETS = ['CountWindowFive231', 'CountWindowSix231', 'CountWindowFour231']
CONTROLLERS = ['count_table_batch.py', 'runner.py', 'replay.py', 'develop_lean.py',
               'prepare_count_higher_tables.py', 'prepare_count_triples_table.py']


def lock():
    import msvcrt
    JOB.mkdir(parents=True, exist_ok=True)
    handle = (JOB / 'worker.lock').open('a+b')
    handle.seek(0); handle.write(b'0'); handle.flush(); handle.seek(0)
    msvcrt.locking(handle.fileno(), msvcrt.LK_NBLCK, 1)
    return handle


def prepare(refresh=False):
    held = lock()
    try:
        exists = (JOB / 'manifest.json').exists()
        assert not exists or refresh, 'Existing batch: use run or prepare --refresh'
        original = r.read(r.HERE / 'runtime/manifest.json'); r.validate(original)
        config = original['config'].copy()
        commit = r.git('rev-parse', 'HEAD').decode().strip()
        config.update(source_commit=commit, timeout_seconds=1800, thread_stack_kb=65536,
                      memory_policy='observe_only')
        state = r.read(JOB / 'state.json') if exists else dict(completed={}, failures=[])
        if exists:
            previous = r.read(JOB / 'manifest.json')
            for name, row in previous['modules'].items():
                assert r.digest(SRC / (name.replace('.', '/') + '.lean')) == row['source_sha256']
            history = JOB / 'history' / str(time.time_ns())
            r.atomic(history / 'manifest.json', previous); r.atomic(history / 'state.json', state)
            if state.get('latest_log') and Path(state['latest_log']).exists():
                shutil.copyfile(state['latest_log'], history / 'last-module.log')
        tracked = set(r.git('ls-tree', '-r', '--name-only', commit).decode().splitlines())
        modules = {}
        def freeze(name):
            if name.startswith(('Std', 'Init', 'Lean', 'Mathlib')):
                return None
            if name in modules:
                return modules[name]['closure_hash']
            rel = name.replace('.', '/') + '.lean'
            source = next((folder + '/' + rel for folder in SEARCH if folder + '/' + rel in tracked), None)
            assert source, ('Missing committed source', name)
            data = r.blob(commit, source)
            deps = {}
            for line in data.decode().splitlines():
                if line.startswith('import '):
                    for dep in line.split('--')[0].split()[1:]:
                        value = freeze(dep)
                        if value:
                            deps[dep] = value
            sha = r.hashbytes(data)
            fingerprint = r.hashbytes(json.dumps([sha, deps, config['lean_version'], config['tools'],
                                                  config['mathlib_commit']], sort_keys=True).encode())
            dest = SRC / rel; dest.parent.mkdir(parents=True, exist_ok=True); dest.write_bytes(data)
            modules[name] = dict(source_path=source, source_sha256=sha, dependency_hashes=deps,
                                 closure_hash=fingerprint)
            return fingerprint
        for target in TARGETS:
            freeze(target)
        controllers = {str(r.HERE / 'scripts' / name): r.digest(r.HERE / 'scripts' / name) for name in CONTROLLERS}
        for path in controllers:
            rel = Path(path).relative_to(r.ROOT).as_posix()
            assert r.blob(commit, rel) == Path(path).read_bytes().replace(b'\r\n', b'\n'), ('Uncommitted controller', path)
        donor = r.read(DONOR / 'state.json')
        r.atomic(JOB / 'donor-state.json', donor)
        donor_hash = r.digest(JOB / 'donor-state.json')
        donor_rows = {**donor.get('base_dependencies', {}), **donor['completed']}
        reused = 0
        for name, row in modules.items():
            src = DONOR / 'src' / (name.replace('.', '/') + '.lean')
            old = donor_rows.get(name)
            if not old or old['closure_hash'] != row['closure_hash']:
                continue
            assert r.digest(src) == row['source_sha256']
            assert r.digest(src.with_suffix('.olean')) == old['artifact_sha256']
            shutil.copyfile(src.with_suffix('.olean'), (SRC / (name.replace('.', '/') + '.olean')))
            state['completed'][name] = dict(old, reused_from=str(DONOR),
                                           donor_state_sha256=donor_hash)
            reused += 1
        manifest = dict(source_commit=commit, config=config, modules=modules, controllers=controllers,
                        targets=TARGETS, original_manifest_sha256=r.digest(r.HERE / 'runtime/manifest.json'),
                        scope='Complete table coverage, with explicit local refutation premises; not a final fresh build')
        state.update(status='prepared', source_commit=commit, targets=TARGETS, coverage_results={},
                     current=None, failure=None, prepared=r.now(), total_modules=len(modules),
                     reused_dependencies=reused, global_231='UNRESOLVED')
        r.atomic(JOB / 'manifest.json', manifest); r.atomic(JOB / 'state.json', state)
        print(json.dumps(dict(source_commit=commit, modules=len(modules), reused=reused)))
    finally:
        held.close()


def validate(manifest):
    for path, digest in manifest['controllers'].items():
        assert r.digest(path) == digest, ('Changed controller', path)
    assert r.digest(r.HERE / 'runtime/manifest.json') == manifest['original_manifest_sha256']
    r.validate(r.read(r.HERE / 'runtime/manifest.json'))
    for name, row in manifest['modules'].items():
        assert r.digest(SRC / (name.replace('.', '/') + '.lean')) == row['source_sha256'], name


def run():
    held = lock(); manifest = r.read(JOB / 'manifest.json'); validate(manifest)
    state = r.read(JOB / 'state.json'); config = manifest['config']; checked = set()
    env = r.process_context(config)
    excluded = os.path.normcase(str(r.HERE / 'build/frozen/src'))
    env['LEAN_PATH'] = os.pathsep.join([str(SRC), *[p for p in env['LEAN_PATH'].split(os.pathsep)
        if p and os.path.normcase(p) != excluded]])
    state.update(status='running', pid=os.getpid(), started=r.now(), failure=None)
    r.atomic(JOB / 'state.json', state)
    def build(name):
        if name in checked:
            return
        row = manifest['modules'][name]
        for dep in row['dependency_hashes']:
            build(dep)
        source = SRC / (name.replace('.', '/') + '.lean'); output = source.with_suffix('.olean')
        old = state['completed'].get(name)
        if old and old['closure_hash'] == row['closure_hash'] and output.exists() and r.digest(output) == old['artifact_sha256']:
            checked.add(name); return
        if name in TARGETS:
            # A separate development check may still be finishing this exact
            # target. Adopt only matching completed evidence, never duplicate it.
            while True:
                donor = r.read(DONOR / 'state.json')
                match = donor.get('completed', {}).get(name)
                if match and match['closure_hash'] == row['closure_hash']:
                    src = DONOR / 'src' / (name.replace('.', '/') + '.lean')
                    assert r.digest(src) == row['source_sha256']
                    assert r.digest(src.with_suffix('.olean')) == match['artifact_sha256']
                    snapshot = JOB / 'donor-rechecks' / f'{time.time_ns()}.json'
                    r.atomic(snapshot, donor)
                    shutil.copyfile(src.with_suffix('.olean'), output)
                    state['completed'][name] = dict(match, reused_from=str(DONOR),
                                                    donor_state_sha256=r.digest(snapshot))
                    r.atomic(JOB / 'state.json', state); checked.add(name); return
                active = []
                for proc in r.psutil.process_iter(['pid', 'cmdline']):
                    args = proc.info['cmdline'] or []
                    if name in args and any(x.endswith('develop_from_fresh.py') for x in args):
                        active.append(proc.pid)
                if not active:
                    break
                state.update(status='waiting_for_donor', current=name, donor_pids=active,
                             heartbeat=r.now(), child_pid=None)
                r.atomic(JOB / 'state.json', state); time.sleep(5)
        log = JOB / 'logs' / (name.replace('.', '_') + '.log'); log.parent.mkdir(parents=True, exist_ok=True)
        command = [str(Path(config['lean_bin']) / 'lean.exe'), '--tstack=65536', '--root=' + str(SRC),
                   '-o', str(output), str(source)]
        state.update(status='running', current=name, latest_log=str(log), last_progress=r.now()); r.atomic(JOB / 'state.json', state)
        start = time.monotonic(); peak = 0
        with log.open('w', encoding='utf-8') as stream:
            stream.write(json.dumps(command) + '\n'); stream.flush()
            child = subprocess.Popen(command, cwd=SRC, env=env, stdout=stream, stderr=subprocess.STDOUT)
            try:
                while child.poll() is None:
                    try:
                        rss = r.psutil.Process(child.pid).memory_info().rss
                    except r.psutil.NoSuchProcess:
                        rss = 0
                    peak = max(peak, rss)
                    state.update(heartbeat=r.now(), child_pid=child.pid,
                                 resources=dict(rss_mb=round(rss/2**20, 1), peak_rss_mb=round(peak/2**20, 1),
                                                memory_policy='observe_only'))
                    r.atomic(JOB / 'state.json', state)
                    if time.monotonic()-start > config['timeout_seconds']:
                        raise RuntimeError('Module timeout: unresolved')
                    time.sleep(1)
                if child.returncode:
                    raise RuntimeError(f'Lean exit {child.returncode}: {log}')
            except BaseException:
                r.kill_tree(child); child.wait(); raise
        text = log.read_text(encoding='utf-8')
        state['completed'][name] = dict(row, artifact_sha256=r.digest(output), log_sha256=r.digest(log),
            axiom_audits=r.audit_axioms(text), command=command, elapsed_seconds=time.monotonic()-start,
            peak_rss_mb=round(peak/2**20, 1), completed=r.now())
        state['last_progress'] = r.now(); r.atomic(JOB / 'state.json', state)
        checked.add(name); print(name, 'PASS', round(time.monotonic()-start, 2), flush=True)
    try:
        for target in TARGETS:
            build(target)
            row = state['completed'][target]
            audits = row.get('axiom_audits', row.get('axioms', []))
            assert audits, ('Missing target audit', target)
            assert all(set(a['axioms']) <= r.ALLOWED for a in audits)
            state['coverage_results'][target] = dict(closure_hash=row['closure_hash'], axioms=audits)
            r.atomic(JOB / 'state.json', state)
        validate(manifest); state.update(status='coverage_complete', current=None, finished=r.now())
    except BaseException as ex:
        state.update(status='action_required', failure=str(ex))
        state['failures'].append(dict(item=state.get('current'), error=str(ex), time=r.now()))
        traceback.print_exc()
    finally:
        r.atomic(JOB / 'state.json', state); held.close()
    print(json.dumps(dict(status=state['status'], coverage=list(state['coverage_results']), failure=state.get('failure'))))


if __name__ == '__main__':
    parser = argparse.ArgumentParser(); parser.add_argument('mode', choices=['prepare', 'run'])
    parser.add_argument('--refresh', action='store_true'); args = parser.parse_args()
    if args.refresh and args.mode != 'prepare':
        parser.error('--refresh requires prepare')
    prepare(args.refresh) if args.mode == 'prepare' else run()
