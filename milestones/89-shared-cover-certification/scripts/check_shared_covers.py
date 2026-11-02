"""Sequential, resumable kernel checks of the generated shared geometric covers."""
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
generation_path = HERE / 'data/shared-cover-generation.json'
generation = read(generation_path)
assert generation['status'] == 'GENERATED_ALL_SHARED_COVERS_KERNEL_CHECKS_PENDING'
assert sha(HERE / 'scripts/build_shared_covers.py') == generation['script_sha256']
for name, digest in generation['input_sha256'].items():
    assert sha(ROOT / name) == digest
for part in ['build', 'logs', 'data']:
    (HERE / part).mkdir(exist_ok=True)


def verify(base, module):
    rp = base / 'data' / (module + '-audit.json')
    r = read(rp)
    assert r['exit_code'] == 0 and r['status'].startswith('PASS_')
    for sub, ext, key in [('lean', '.lean', 'source_sha256'), ('build', '.olean', 'olean_sha256'),
                          ('logs', '.log', 'log_sha256')]:
        assert sha(base / sub / (module + ext)) == r[key], (module, key)
    return sha(rp)


inherited = {name: verify(OLD, name) for name in ['GraphData', 'CoverTree', 'Boxes']}
paths = [str(HERE / 'build'), *read(OLD / 'data/BoxWitness-audit.json')['paths']]
env = os.environ.copy()
env['PATH'] = str(BIN) + ';' + env['PATH']
env['LEAN_PATH'] = ';'.join(paths)
run_id = str(time.time_ns())
record_path = HERE / 'logs' / ('shared-cover-run-' + run_id + '.json')
record = dict(status='RUNNING', pid=os.getpid(), classes=selected, records=[],
              started_at=datetime.datetime.now(datetime.timezone.utc).isoformat(),
              inherited_receipt_sha256=inherited, generation_sha256=sha(generation_path),
              script_sha256=sha(Path(__file__)),
              scope='Geometric cover equations only; no context-witness or full-key-row theorem.')


def save_record():
    temporary = record_path.with_suffix('.tmp')
    temporary.write_text(json.dumps(record, indent=2) + '\n')
    os.replace(temporary, record_path)


save_record()
try:
    for number in selected:
        label = f'{number:03d}'
        row = generation['classes'][number]
        assert row['dag_set'] == number
        for kind in ['Data', 'Checks']:
            module = f'Cover{label}{kind}'
            src = HERE / 'lean' / (module + '.lean')
            assert sha(src) == row['source_sha256'][src.name]
            rp = HERE / 'data' / (module + '-audit.json')
            dependencies = dict(inherited)
            if kind == 'Checks':
                dependencies[f'Cover{label}Data'] = verify(HERE, f'Cover{label}Data')
            if rp.exists():
                verify(HERE, module)
                saved = read(rp)
                assert saved['dependencies'] == dependencies
                record['records'].append(dict(module=module, status='REUSED_CHECKED_MODULE', receipt_sha256=sha(rp)))
                save_record()
                print(module, 'REUSED', flush=True)
                continue
            obj = HERE / 'build' / (module + '.olean')
            log = HERE / 'logs' / (module + '.log')
            if log.exists():
                (HERE / 'logs' / (module + '-previous-' + sha(log)[:12] + '.log')).write_bytes(log.read_bytes())
            start = time.monotonic()
            with log.open('w', encoding='utf-8') as out:
                proc = subprocess.Popen([str(BIN / 'lake.exe'), 'env', 'lean', '-s', '65536', '-R',
                                         str(HERE / 'lean'), '-o', str(obj.with_suffix('.fresh.olean')), str(src)],
                                        cwd=BIN.parent.parent / 'mathlib', env=env, stdout=out,
                                        stderr=subprocess.STDOUT)
                record['active'] = dict(module=module, launcher_pid=proc.pid, source_sha256=sha(src))
                save_record()
                exit_code = proc.wait()
            result = dict(module=module, exit_code=exit_code, seconds=time.monotonic() - start,
                          source_sha256=sha(src), log_sha256=sha(log), dependencies=dependencies,
                          generation_sha256=sha(generation_path), checker_sha256=sha(Path(__file__)))
            (HERE / 'logs' / (module + '-record.json')).write_text(json.dumps(result, indent=2) + '\n')
            if exit_code:
                record['status'] = 'FAILED_MODULE'
                record['failure'] = result
                save_record()
                print(log.read_text()[-16000:], flush=True)
                raise SystemExit(exit_code)
            text = log.read_text()
            assert 'error:' not in text and 'sorryAx' not in text
            assert not re.search(r'\b(sorry|admit|native_decide)\b', src.read_text())
            audits = re.findall(r"'([^']+)' depends on axioms:\s*\[([^]]*)\]", text, re.S)
            audits += [(n, '') for n in re.findall(r"'([^']+)' does not depend on any axioms", text)]
            assert len(audits) == (1 if kind == 'Checks' else 0)
            checked = []
            for theorem, axioms in audits:
                values = re.findall(r'[A-Za-z][\w.]*', axioms)
                assert not values, (module, values)
                checked.append(dict(theorem=theorem, axioms=values))
            os.replace(obj.with_suffix('.fresh.olean'), obj)
            result.update(status='PASS_SHARED_COVER_KERNEL' if kind == 'Checks' else 'PASS_SHARED_COVER_DATA',
                          olean_sha256=sha(obj), theorem_audits=checked,
                          scope='One shared geometric cover equation only; context witnesses and row identification remain separate.')
            rp.write_text(json.dumps(result, indent=2) + '\n')
            record['records'].append(dict(module=module, status=result['status'], receipt_sha256=sha(rp)))
            record.pop('active', None)
            save_record()
            print(module, result['status'], round(result['seconds'], 3), 'seconds', flush=True)
    record['status'] = 'PASS_SELECTED_SHARED_COVERS'
    record['finished_at'] = datetime.datetime.now(datetime.timezone.utc).isoformat()
    save_record()
    print(record['status'], selected, flush=True)
except BaseException as exc:
    if record['status'] == 'RUNNING':
        record['status'] = 'STOPPED_WITH_EXCEPTION'
        record['exception'] = repr(exc)
        save_record()
    raise
