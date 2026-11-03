"""Resume the fixed 138 proof in dependency order; retain exact attempts."""
from pathlib import Path
import argparse, datetime, hashlib, json, os, re, shutil, subprocess, time

HERE = Path(__file__).resolve().parents[1]
ROOT = HERE.parents[1]
BIN = Path('D:/Codex/2026-10-01/it-should-have-a-property-of/work/lean-research/lean-4.19.0-windows/bin')

read = lambda p: json.loads(p.read_text(encoding='utf-8-sig'))
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
now = lambda: datetime.datetime.now(datetime.timezone.utc).isoformat()
parser = argparse.ArgumentParser()
parser.add_argument('--case', choices=['base','short'], required=True)
parser.add_argument('--limit', type=int)
parser.add_argument('--timeout', type=int, default=600)
args = parser.parse_args()
assert args.timeout > 0
BUILD = HERE / ('build-'+args.case)
planfile = HERE / ('data/proof-plan-'+args.case+'.json')
plan = read(planfile)
assert plan['status'] == 'EXPORTED_AND_SIMULATED_LEAN_PENDING'
assert plan['stats']['simulated'] and plan['stats']['slots'] <= 8191
CNF=plan['cnf_module']
FINAL=plan['final_module']
environment_file = HERE.parent / '125-critical-six-count/data/environment-sum.json'
environment = read(environment_file)
paths = [str(BUILD), str(HERE / 'build-independent')] + environment['paths']
env = os.environ.copy()
env['PATH'] = str(BIN) + ';' + env['PATH']
env['LEAN_PATH'] = ';'.join(paths)
source_hashes = {a['path']: a['sha256'] for a in plan['artifacts']}
modules = set(plan['module_order'])
sources = {m: HERE / 'lean' / (m.replace('.', '/') + '.lean') for m in modules}
fixed = {str(planfile): sha(planfile), str(environment_file): sha(environment_file),
         str(Path(__file__)): sha(Path(__file__)),
         str(BIN / 'lean.exe'): sha(BIN / 'lean.exe'),
         str(BIN / 'lake.exe'): sha(BIN / 'lake.exe')}
for path, digest in environment['receipts'].items():
    assert sha(ROOT / path) == digest
    fixed[str(ROOT / path)] = digest
for key in ['checker_object', 'checker_receipt']:
    path = Path(plan[key])
    assert sha(path) == plan[key + '_sha256']
    fixed[str(path)] = sha(path)
for m, src in sources.items():
    assert sha(src) == source_hashes[src.relative_to(HERE).as_posix()]
    assert not re.search(r'\b(sorry|admit|native_decide|axiom)\b', src.read_text(encoding='utf-8'))
ordered, seen, visiting = [], set(), set()
def visit(m):
    if m in seen:
        return
    assert m not in visiting
    visiting.add(m)
    for dep in re.findall(r'^import ([\w.]+)$', sources[m].read_text(encoding='utf-8'), re.M):
        if dep in modules:
            visit(dep)
    visiting.remove(m)
    seen.add(m)
    ordered.append(m)
visit(FINAL)
assert seen == modules, (sorted(modules-seen), FINAL)
run = str(time.time_ns())
runfile = HERE / 'logs' / ('replay-'+args.case+'-' + run + '.json')
progress = HERE / ('data/replay-progress-'+args.case+'.json')
lock = HERE / ('data/replay-'+args.case+'.lock')
attempt = HERE / 'logs' / ('replay-attempt-' + run)
attempt.mkdir(parents=True)
(attempt / 'checker.py.txt').write_bytes(Path(__file__).read_bytes())
with lock.open('x', encoding='utf-8') as out:
    json.dump(dict(pid=os.getpid(), run_record=str(runfile)), out)
state = dict(status='RUNNING', pid=os.getpid(), started_at=now(), active=None,
             total_modules=len(ordered), checked_modules=[], paths=paths,
             fixed_dependencies=fixed, ordered_modules=ordered,
             scope='Selected window proof chain. Check the final theorem statement and printed axioms; numerical graph bounds remain separate.')
def save():
    state['updated_at'] = now()
    content = json.dumps(state, indent=2) + '\n'
    for target in [runfile, progress]:
        temp = target.with_suffix('.tmp')
        temp.write_text(content, encoding='utf-8')
        os.replace(temp, target)
def check_hashes(mapping):
    for path, digest in mapping.items():
        assert sha(Path(path)) == digest, path
def object_path(m):
    return BUILD / (m.replace('.', '/') + '.olean')
def receipt_path(m):
    name = m + '-audit.json'
    return HERE / 'data' / name
def checked(m):
    rp = receipt_path(m)
    if not rp.exists():
        return None
    r = read(rp)
    assert r['exit_code'] == 0 and not r.get('timeout', False)
    assert r['status'] == 'PASS_WINDOW_REPLAY_MODULE'
    assert sha(sources[m]) == r['source_sha256']
    object_digest = r['olean_sha256']
    assert sha(object_path(m)) == object_digest
    log = Path(r['log'])
    if not log.is_absolute():
        log = HERE / log
    assert sha(log) == r['log_sha256']
    snapshot = Path(r['source_snapshot'])
    if not snapshot.is_absolute():
        snapshot = HERE / snapshot
    assert sha(snapshot) == r['source_sha256']
    for path, digest in r['dependencies'].items():
        dep = Path(path)
        if not dep.is_absolute():
            dep = ROOT / dep
        assert sha(dep) == digest, path
    for a in r.get('theorem_audits', []):
        assert set(a['axioms']) <= {'propext', 'Classical.choice', 'Quot.sound'}
    return dict(module=m, receipt_sha256=sha(rp), seconds=r['seconds'],
                theorem_audits=len(r.get('theorem_audits', [])))
def dependencies(m):
    deps = dict(fixed)
    for name in re.findall(r'^import ([\w.]+)$', sources[m].read_text(encoding='utf-8'), re.M):
        if name in modules:
            assert checked(name) is not None, name
            deps[str(receipt_path(name))] = sha(receipt_path(name))
            deps[str(object_path(name))] = sha(object_path(name))
        else:
            obj = next((Path(p) / (name.replace('.', '/') + '.olean') for p in paths
                        if (Path(p) / (name.replace('.', '/') + '.olean')).exists()), None)
            assert obj is not None, name
            deps[str(obj)] = sha(obj)
            if name == 'LratFast':
                assert obj == Path(plan['checker_object'])
    return deps
def gate(m):
    command = "$o=Get-CimInstance Win32_OperatingSystem; $p=@(Get-CimInstance Win32_Process -Filter \"Name='lean.exe'\" | Select-Object ProcessId,PrivatePageCount); @{free_bytes=[long]$o.FreePhysicalMemory*1024;processes=$p}|ConvertTo-Json -Depth 3 -Compress"
    while True:
        s = json.loads(subprocess.check_output(['powershell', '-NoProfile', '-Command', command], text=True))
        state['resources'] = s
        if s['free_bytes'] >= 1.5 * 1024**3 and len(s['processes']) <= 2:
            return
        state.update(status='WAITING_FOR_RESOURCES', waiting_for=m)
        save()
        time.sleep(10)
save()
new = 0
try:
    for m in ordered:
        receipt = checked(m)
        if receipt is None:
            if args.limit is not None and new >= args.limit:
                state['status'] = 'PASS_BOUNDED_PREFIX'
                break
            gate(m)
            check_hashes(fixed)
            src = sources[m]
            before = sha(src)
            assert before == source_hashes[src.relative_to(HERE).as_posix()]
            deps = dependencies(m)
            snap = attempt / (m + '.lean.txt')
            snap.write_bytes(src.read_bytes())
            obj = object_path(m)
            obj.parent.mkdir(parents=True, exist_ok=True)
            fresh = obj.with_suffix('.' + run + '.olean')
            log = HERE / 'logs' / (m + '-' + run + '.log')
            command = [str(BIN / 'lake.exe'), 'env', 'lean', '-s', '65536', '-R', str(HERE / 'lean'), '-o', str(fresh), str(src)]
            start, timedout = time.monotonic(), False
            with log.open('w', encoding='utf-8') as out:
                proc = subprocess.Popen(command, cwd=BIN.parent.parent / 'mathlib', env=env,
                                        stdout=out, stderr=subprocess.STDOUT)
                state.update(status='RUNNING', active=dict(module=m, pid=proc.pid, log=str(log)), waiting_for=None)
                save()
                try:
                    code = proc.wait(timeout=args.timeout)
                except subprocess.TimeoutExpired:
                    timedout = True
                    subprocess.run(['taskkill', '/PID', str(proc.pid), '/T', '/F'],
                                   stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL, check=False)
                    code = proc.wait(timeout=30)
            state['active'] = None
            r = dict(module=m, exit_code=code, timeout=timedout, seconds=time.monotonic()-start,
                     source_sha256=before, source_snapshot=snap.relative_to(HERE).as_posix(),
                     log=log.relative_to(HERE).as_posix(), log_sha256=sha(log), dependencies=deps,
                     command=command, paths=paths, resource_snapshot=state['resources'],
                     checker_sha256=fixed[str(Path(__file__))])
            record = HERE / 'logs' / (m + '-' + run + '-record.json')
            record.write_text(json.dumps(r, indent=2) + '\n', encoding='utf-8')
            assert code == 0 and not timedout, (m, code, timedout, str(log))
            check_hashes(deps)
            assert sha(src) == before == sha(snap)
            output = log.read_text(encoding='utf-8')
            assert 'error:' not in output and 'sorryAx' not in output
            rows = re.findall(r"'([^']+)' depends on axioms:\s*\[([^]]*)\]", output, re.S)
            rows += [(n, '') for n in re.findall(r"'([^']+)' does not depend on any axioms", output)]
            assert len(rows) == src.read_text(encoding='utf-8').count('#print axioms')
            audits = []
            for theorem, ax in rows:
                axioms = re.findall(r'[A-Za-z][\w.]*', ax)
                assert set(axioms) <= {'propext', 'Classical.choice', 'Quot.sound'}
                audits.append(dict(theorem=theorem, axioms=axioms))
            if m == FINAL:
                assert any(a['theorem'] == plan['final_theorem'] for a in audits)
            os.replace(fresh, obj)
            r.update(status='PASS_WINDOW_REPLAY_MODULE', olean_sha256=sha(obj), theorem_audits=audits)
            receipt_path(m).write_text(json.dumps(r, indent=2) + '\n', encoding='utf-8')
            receipt = checked(m)
            assert receipt is not None
            new += 1
        state['checked_modules'].append(receipt)
        save()
        print('CHECKED', len(state['checked_modules']), '/', len(ordered), m, flush=True)
    else:
        state['status'] = 'PASS_COMPLETE_WINDOW_REFUTATION'
except BaseException as exc:
    state.update(status='STOPPED', exception=repr(exc))
    raise
finally:
    state['finished_at'] = now()
    save()
    if state['active'] is None:
        lock.unlink()
