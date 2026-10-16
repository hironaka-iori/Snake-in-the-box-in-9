"""Check regrowth certificates with durable, resumable per-module progress.

Lake validates and reuses compiled modules. Every attempt has separate logs;
the latest manifest is an atomic snapshot, while events are append-only.
Only a complete aggregate, optional consequences, source check and axiom audit
can produce PASSED. Existing caches alone never establish success.
"""
import argparse
from concurrent.futures import ThreadPoolExecutor, as_completed
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import sys
import threading
import time
import traceback

ROOT = Path(__file__).resolve().parent.parent
LEAN = ROOT / 'work/final_lean'


def utc():
    return datetime.now(timezone.utc).isoformat()


def atomic_json(path, data):
    temporary = path.with_suffix('.tmp')
    with temporary.open('w', encoding='utf-8', newline='\n') as out:
        json.dump(data, out, indent=2)
        out.write('\n')
        out.flush()
        os.fsync(out.fileno())
    # Windows readers and antivirus scanners can briefly deny replacement.
    # Keep the fully flushed temporary file and retry rather than losing progress.
    for attempt in range(101):
        try:
            os.replace(temporary, path)
            break
        except PermissionError:
            if attempt == 100:
                raise
            time.sleep(0.05)


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('tag', help='e.g. 144v2')
    ap.add_argument('--workers', type=int, default=2)
    ap.add_argument('--lake', default=os.environ.get('LAKE', 'lake'))
    ap.add_argument('--results-module', help='Optional final consequence module')
    ap.add_argument('--audit-theorem', action='append', default=[],
                    help='Additional fully qualified theorem to audit')
    args = ap.parse_args()
    if not re.fullmatch(r'\d+(?:v2)?', args.tag) or args.workers < 1:
        ap.error('invalid tag or worker count')
    if args.results_module and not re.fullmatch(r'\w+', args.results_module):
        ap.error('invalid results module')
    if args.audit_theorem and not args.results_module:
        ap.error('additional audit theorems require --results-module')
    if any(not re.fullmatch(r'[\w.]+', n) for n in args.audit_theorem):
        ap.error('invalid theorem name')
    aggregate = f'DfsBankCert{args.tag}'
    source = LEAN / f'{aggregate}.lean'
    targets = re.findall(r'^import (DfsBankCert\w+)$', source.read_text(), re.M)
    if not targets:
        raise RuntimeError('Aggregate has no certificate dependencies')
    folder = ROOT / 'outputs' / f'dfs-lean-{args.tag}'
    run_id = datetime.now(timezone.utc).strftime('%Y%m%dT%H%M%S') + f'-{os.getpid()}'
    run_folder = folder / 'runs' / run_id
    run_folder.mkdir(parents=True)
    files = list(LEAN.glob('*.lean')) + [LEAN/'lakefile.toml', LEAN/'lean-toolchain']
    dependencies = sorted(f.stem for f in LEAN.glob(aggregate+'_*.lean'))
    compiled_folder = LEAN / '.lake/build/lib/lean'
    initial_cache = [n for n in dependencies if (compiled_folder/(n+'.olean')).is_file()]
    manifest = dict(tag=args.tag, status='RUNNING', workers=args.workers,
        pid=os.getpid(), run_id=run_id, started_utc=utc(), updated_utc=utc(),
        log_directory=str(run_folder.relative_to(ROOT)),
        sources_sha256={f.name: hashlib.sha256(f.read_bytes()).hexdigest() for f in files},
        dependency_modules_total=len(dependencies), targets_total=len(targets),
        initial_cached_modules=initial_cache, module_events={}, active={},
        completed={}, aggregate=None, results_module=args.results_module, results=None,
        cache_scope='Available caches are provisional until Lake validates each dependency.')
    lock = threading.Lock()

    def save_locked():
        manifest['updated_utc'] = utc()
        atomic_json(run_folder/'manifest.json', manifest)
        atomic_json(folder/'manifest.json', manifest)

    def event_locked(event):
        event = dict(time_utc=utc(), **event)
        with (run_folder/'events.jsonl').open('a', encoding='utf-8', newline='\n') as out:
            out.write(json.dumps(event)+'\n')
            out.flush()
            os.fsync(out.fileno())
        save_locked()

    with lock:
        event_locked(dict(event='started', cached_modules=len(initial_cache)))

    def build(module):
        start = time.monotonic()
        log = run_folder/f'{module}.log'
        with log.open('w', encoding='utf-8', newline='\n') as out:
            child = subprocess.Popen([args.lake, 'build', module], cwd=LEAN,
                stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                text=True, encoding='utf-8', errors='replace', bufsize=1)
            with lock:
                manifest['active'][module] = dict(pid=child.pid, started_utc=utc())
                event_locked(dict(event='target_started', module=module, pid=child.pid))
            for line in child.stdout:
                out.write(line)
                out.flush()
                match = re.search(r'\b(Built|Replayed)\s+(\w+)', line)
                if match:
                    state, name = match.groups()
                    if name.startswith(aggregate):
                        os.fsync(out.fileno())
                        with lock:
                            manifest['module_events'][name] = dict(result=state, time_utc=utc())
                            event_locked(dict(event='module_completed', module=name, result=state))
            returncode = child.wait()
            out.flush()
            os.fsync(out.fileno())
        result = dict(returncode=returncode, seconds=round(time.monotonic()-start, 3),
                      log=str(log.relative_to(ROOT)))
        with lock:
            manifest['active'].pop(module, None)
            manifest['completed'][module] = result
            event_locked(dict(event='target_completed', module=module, **result))
        return result

    def finish(status, **fields):
        with lock:
            manifest.update(status=status, finished_utc=utc(), **fields)
            event_locked(dict(event='finished', status=status))
        print(json.dumps(dict(status=status, run_id=run_id,
                              manifest=str((folder/'manifest.json').relative_to(ROOT)))), flush=True)
        return 0 if status == 'PASSED' else 1

    try:
        with ThreadPoolExecutor(max_workers=args.workers) as pool:
            futures = {pool.submit(build, target): target for target in targets}
            count = 0
            for future in as_completed(futures):
                target = futures[future]
                try:
                    result = future.result()
                except Exception as exc:
                    result = dict(returncode=-1, error=repr(exc), traceback=traceback.format_exc())
                    with lock:
                        manifest['active'].pop(target, None)
                        manifest['completed'][target] = result
                        event_locked(dict(event='target_error', module=target, **result))
                count += 1
                print(f'{count}/{len(targets)} {target}: {result["returncode"]}', flush=True)
        if any(manifest['completed'][target]['returncode'] for target in targets):
            return finish('FAILED', failure_stage='dependencies')
        manifest['aggregate'] = build(aggregate)
        if manifest['aggregate']['returncode']:
            return finish('FAILED', failure_stage='aggregate')
        if args.results_module:
            manifest['results'] = build(args.results_module)
            if manifest['results']['returncode']:
                return finish('FAILED', failure_stage='results')
        names = [f'Snake9.Dfs.bank_no192_keep{args.tag}'] + args.audit_theorem
        audit = run_folder/'Audit.lean'
        audit.write_text(f'import {args.results_module or aggregate}\n'+
                         ''.join(f'#print axioms {name}\n' for name in names), encoding='utf-8')
        r = subprocess.run([args.lake, 'env', 'lean', str(audit)], cwd=LEAN,
                           capture_output=True, text=True, encoding='utf-8', errors='replace')
        (run_folder/'axioms.log').write_text(r.stdout+r.stderr, encoding='utf-8')
        audits = re.findall(r"'([^']+)' depends on axioms: \[([^]]*)\]", r.stdout)
        audit_map = {name: [a.strip() for a in axioms.split(',') if a.strip()]
                     for name, axioms in audits}
        allowed = {'propext', 'Classical.choice', 'Quot.sound'}
        good = r.returncode == 0 and len(audits) == len(names) and set(audit_map) == set(names)
        good = good and all(set(axioms) <= allowed for axioms in audit_map.values())
        unchanged = all(hashlib.sha256((LEAN/name).read_bytes()).hexdigest() == digest
                        for name, digest in manifest['sources_sha256'].items())
        missing = [n for n in dependencies if not (compiled_folder/(n+'.olean')).is_file()]
        return finish('PASSED' if good and unchanged and not missing else 'FAILED',
            axioms=audit_map, sources_unchanged=unchanged, missing_modules=missing,
            axiom_audit_log=str((run_folder/'axioms.log').relative_to(ROOT)))
    except Exception as exc:
        return finish('FAILED', failure_stage='runner', error=repr(exc))


if __name__ == '__main__':
    sys.exit(main())
