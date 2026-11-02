"""Check balanced tables and shared covers in one resumable sequential process."""
from pathlib import Path
import argparse, datetime, hashlib, json, os, re, subprocess, time

HERE = Path(__file__).resolve().parents[1]
ROOT = HERE.parents[1]
OLD = ROOT / 'milestones/88-retention-diagram-certificate'
BIN = Path('D:/Codex/2026-10-01/it-should-have-a-property-of/work/lean-research/lean-4.19.0-windows/bin')
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
read = lambda p: json.loads(p.read_text())
parser = argparse.ArgumentParser()
parser.add_argument('--classes', default='all')
args = parser.parse_args()
selected = list(range(127)) if args.classes == 'all' else [int(x) for x in args.classes.split(',')]
assert len(set(selected)) == len(selected) and all(0 <= x < 127 for x in selected)
generation = read(HERE / 'data/balanced-cover-generation.json')
ordinary = read(HERE / 'data/shared-cover-generation.json')
for gen, script in [(generation, 'build_balanced_covers.py'), (ordinary, 'build_shared_covers.py')]:
    assert sha(HERE / 'scripts' / script) == gen['script_sha256']
    for name, digest in gen['input_sha256'].items():
        assert sha(ROOT / name) == digest


def verify(base, module):
    rp = base / 'data' / (module + '-audit.json')
    r = read(rp)
    assert r['exit_code'] == 0 and r['status'].startswith('PASS_')
    for sub, ext, key in [('lean', '.lean', 'source_sha256'), ('build', '.olean', 'olean_sha256'),
                          ('logs', '.log', 'log_sha256')]:
        assert sha(base / sub / (module + ext)) == r[key], (module, key)
    return str(rp.relative_to(ROOT)), sha(rp)


base_dependencies = dict(verify(OLD, n) for n in ['Boxes', 'CoverTree', 'GraphData'])
base_dependencies.update(dict(verify(HERE, n) for n in ['BalancedLookup', 'LookupCover']))
env = os.environ.copy()
env['PATH'] = str(BIN) + ';' + env['PATH']
env['LEAN_PATH'] = ';'.join([str(HERE / 'build'), str(OLD / 'build')])
run_id = str(time.time_ns())
record_path = HERE / 'logs' / ('balanced-cover-run-' + run_id + '.json')
lock_path = HERE / 'data/balanced-cover-active.json'
lock = dict(pid=os.getpid(), run_id=run_id, record=str(record_path))
with lock_path.open('x') as out:
    json.dump(lock, out)
record = dict(status='RUNNING', pid=os.getpid(), classes=selected, records=[],
              started_at=datetime.datetime.now(datetime.timezone.utc).isoformat(),
              base_dependencies=base_dependencies, generation_sha256=sha(HERE / 'data/balanced-cover-generation.json'),
              script_sha256=sha(Path(__file__)),
              scope='Balanced-table identities and geometric cover equations. Context witnesses and graph interpretation remain separate.')


def save():
    temporary = record_path.with_suffix('.tmp')
    temporary.write_text(json.dumps(record, indent=2) + '\n')
    os.replace(temporary, record_path)


def check_module(module, dependencies, expected_audits, expected_source):
    src = HERE / 'lean' / (module + '.lean')
    assert sha(src) == expected_source
    pins = dict(base_dependencies)
    pins.update(dict(verify(HERE, dep) for dep in dependencies))
    rp = HERE / 'data' / (module + '-audit.json')
    if rp.exists():
        verify(HERE, module)
        # Ordinary CoverNNNData may have a successful receipt from the earlier driver.
        old = read(rp)
        if not (module.startswith('Cover') and module.endswith('Data')):
            assert old['dependencies'] == pins
        record['records'].append(dict(module=module, status='REUSED_CHECKED_MODULE', receipt_sha256=sha(rp)))
        save()
        print(module, 'REUSED', flush=True)
        return
    obj = HERE / 'build' / (module + '.olean')
    log = HERE / 'logs' / (module + '.log')
    if log.exists():
        (HERE / 'logs' / (module + '-previous-' + sha(log)[:12] + '.log')).write_bytes(log.read_bytes())
    start = time.monotonic()
    with log.open('w', encoding='utf-8') as out:
        proc = subprocess.Popen([str(BIN / 'lake.exe'), 'env', 'lean', '-s', '65536', '-R',
                                 str(HERE / 'lean'), '-o', str(obj.with_suffix('.fresh.olean')), str(src)],
                                cwd=BIN.parent.parent / 'mathlib', env=env, stdout=out, stderr=subprocess.STDOUT)
        record['active'] = dict(module=module, launcher_pid=proc.pid, source_sha256=sha(src))
        save()
        exit_code = proc.wait()
    result = dict(module=module, exit_code=exit_code, seconds=time.monotonic() - start,
                  source_sha256=sha(src), log_sha256=sha(log), dependencies=pins,
                  checker_sha256=sha(Path(__file__)))
    (HERE / 'logs' / (module + '-record.json')).write_text(json.dumps(result, indent=2) + '\n')
    if exit_code:
        record['failure'] = result
        print(log.read_text()[-16000:], flush=True)
        raise RuntimeError(f'{module}: exit {exit_code}')
    text = log.read_text()
    assert 'error:' not in text and 'sorryAx' not in text
    assert not re.search(r'\b(sorry|admit|native_decide)\b', src.read_text())
    audits = re.findall(r"'([^']+)' depends on axioms:\s*\[([^]]*)\]", text, re.S)
    audits += [(n, '') for n in re.findall(r"'([^']+)' does not depend on any axioms", text)]
    assert len(audits) == expected_audits == src.read_text().count('#print axioms')
    checked = []
    for theorem, axioms in audits:
        values = re.findall(r'[A-Za-z][\w.]*', axioms)
        assert set(values) <= {'propext', 'Classical.choice', 'Quot.sound'}
        if theorem.split('.')[-1].startswith('balancedCover') or theorem.split('.')[-1].endswith('_valid'):
            assert not values, (theorem, values)
        checked.append(dict(theorem=theorem, axioms=values))
    os.replace(obj.with_suffix('.fresh.olean'), obj)
    result.update(status='PASS_BALANCED_COVER_KERNEL' if expected_audits else 'PASS_BALANCED_COVER_DATA',
                  olean_sha256=sha(obj), theorem_audits=checked,
                  scope='Balanced lookup data, table identities or one geometric cover; no complete context witness or graph-row theorem.')
    rp.write_text(json.dumps(result, indent=2) + '\n')
    record['records'].append(dict(module=module, status=result['status'], receipt_sha256=sha(rp)))
    record.pop('active', None)
    save()
    print(module, result['status'], round(result['seconds'], 3), 'seconds', flush=True)


save()
try:
    for module, deps, audits in [('BalancedGraphData', [], 0), ('BalancedGraphChecks', ['BalancedGraphData'], 3)]:
        check_module(module, deps, audits, generation['source_sha256'][module + '.lean'])
    for number in selected:
        label = f'{number:03d}'
        module = f'Cover{label}Data'
        check_module(module, [], 0, ordinary['classes'][number]['source_sha256'][module + '.lean'])
        module = f'Balanced{label}Data'
        check_module(module, [f'Cover{label}Data'], 0, generation['source_sha256'][module + '.lean'])
        module = f'Balanced{label}Checks'
        check_module(module, [f'Balanced{label}Data', 'BalancedGraphChecks'], 4, generation['source_sha256'][module + '.lean'])
    record['status'] = 'PASS_SELECTED_BALANCED_COVERS'
    record['finished_at'] = datetime.datetime.now(datetime.timezone.utc).isoformat()
    save()
    print(record['status'], len(selected), 'classes', flush=True)
except BaseException as exc:
    record['status'] = 'STOPPED_WITH_EXCEPTION'
    record['exception'] = repr(exc)
    save()
    raise
finally:
    if lock_path.exists() and read(lock_path) == lock:
        lock_path.unlink()
