"""One isolated, resource-gated check of the actual selected-corner bound."""
from pathlib import Path
import hashlib, json, os, re, subprocess, sys, time

HERE = Path(__file__).resolve().parents[1]
ROOT = HERE.parents[1]
BIN = Path('D:/Codex/2026-10-01/it-should-have-a-property-of/work/lean-research/lean-4.19.0-windows/bin')
MATHLIB = BIN.parent.parent / 'mathlib'
SOURCE = HERE / 'lean/OddPair130.lean'
ENVIRONMENT = ROOT / 'milestones/125-critical-six-count/data/environment-sum.json'
sha = lambda p: hashlib.sha256(Path(p).read_bytes()).hexdigest()
read = lambda p: json.loads(Path(p).read_text(encoding='utf-8-sig'))
run = str(time.time_ns())
attempt = HERE / 'logs' / ('odd-pair-' + run)
attempt.mkdir(parents=True)
build = HERE / 'build-independent'
build.mkdir(exist_ok=True)
record = attempt / 'record.json'
state = dict(status='NOT_STARTED', source_sha256=sha(SOURCE),
             checker_sha256=sha(__file__), started_at_ns=time.time_ns(), pid=os.getpid())

def save():
    record.write_text(json.dumps(state, indent=2) + '\n', encoding='utf-8')

def resource_snapshot():
    command = "$osInfo = Get-CimInstance Win32_OperatingSystem; $leanProcesses = @(Get-CimInstance Win32_Process -Filter \"Name='lean.exe'\" | Select-Object ProcessId,PrivatePageCount); @{available_bytes=([long]$osInfo.FreePhysicalMemory*1024); lean_processes=$leanProcesses} | ConvertTo-Json -Depth 3 -Compress"
    return read_resource(subprocess.check_output(
        ['powershell', '-NoProfile', '-Command', command], text=True))

def read_resource(raw):
    resource = json.loads(raw)
    if isinstance(resource['lean_processes'], dict):
        resource['lean_processes'] = [resource['lean_processes']]
    return resource

try:
    environment = read(ENVIRONMENT)
    environment['paths'] = [str(HERE / 'build-independent')] + environment['paths']
    dependencies = {str(ENVIRONMENT): sha(ENVIRONMENT)}
    for path, digest in environment['receipts'].items():
        resolved = ROOT / path
        assert sha(resolved) == digest, ('Environment pin changed', str(resolved))
        dependencies[str(resolved)] = digest
    prior = ROOT / 'milestones/125-critical-six-count'
    receipt_path = prior / 'data/ActualBounds125-audit.json'
    receipt = read(receipt_path)
    assert receipt['exit_code'] == 0 and receipt['status'] == 'PASS_REFERENCE_RECOVERY_MODULE'
    for path, digest in [
        (prior / 'lean/ActualBounds125.lean', receipt['source_sha256']),
        (prior / 'build-isolated/ActualBounds125.olean', receipt['olean_sha256']),
        (prior / receipt['log'], receipt['log_sha256'])]:
        assert sha(path) == digest, ('ActualBounds125 pin changed', str(path))
        dependencies[str(path)] = digest
    dependencies[str(receipt_path)] = sha(receipt_path)
    parity_receipt_path = HERE / 'data/independent-parity-dependency-audit.json'
    parity_receipt = read(parity_receipt_path)
    assert parity_receipt['status'] == 'PASS' and parity_receipt['exit_code'] == 0
    for path, digest in [(HERE / 'lean/DfsParity.lean', parity_receipt['source_sha256']),
                         (Path(parity_receipt['importable_object']), parity_receipt['importable_object_sha256']),
                         (Path(parity_receipt['log']), parity_receipt['log_sha256']),
                         (HERE / 'audit/check_parity_dependency.py', parity_receipt['checker_sha256'])]:
        assert sha(path) == digest
        dependencies[str(path)] = digest
    dependencies[str(parity_receipt_path)] = sha(parity_receipt_path)
    endpoint_review_path = ROOT / 'milestones/129-fourth-count-three/data/endpoint122-completion-review.json'
    endpoint_review = read(endpoint_review_path)
    assert endpoint_review['status'] == 'PASS_448_ENDPOINT_MODULE_RECEIPTS_AND_ACTUAL_ASSEMBLY'
    dependencies[str(endpoint_review_path)] = sha(endpoint_review_path)
    for name in ['milestones/122-endpoint-equality/lean/ActualEndpoint122.lean',
                 'milestones/122-endpoint-equality/build-isolated/ActualEndpoint122.olean',
                 'milestones/122-endpoint-equality/data/ActualEndpoint122-audit.json',
                 'milestones/121-replacement-window-pressure/build-isolated/ActualPair121.olean']:
        path = ROOT / name
        digest = endpoint_review['source_files_sha256'][name]
        assert sha(path) == digest
        dependencies[str(path)] = digest
    for name in re.findall(r'^import ([\w.]+)$', SOURCE.read_text(), re.M):
        rel = Path(*name.split('.')).with_suffix('.olean')
        path = next((Path(p)/rel for p in environment['paths'] if (Path(p)/rel).exists()), None)
        assert path is not None, ('Missing import', name)
        dependencies[str(path)] = sha(path)
    for path in [ROOT / 'milestones/31-joint-counter-soundness/lean/JointCountTags.lean',
                 ROOT / 'milestones/31-joint-counter-soundness/lean/JointCountBridge.lean',
                 ROOT / 'milestones/127-direct-cardinality/data/next-pair-task.json',
                 MATHLIB / 'lean-toolchain', MATHLIB / 'lake-manifest.json',
                 BIN / 'lean.exe', BIN / 'lake.exe']:
        dependencies[str(path)] = sha(path)
    state['dependencies'] = dependencies
    state['paths'] = environment['paths']
    (attempt / 'source.lean.txt').write_bytes(SOURCE.read_bytes())
    (attempt / 'checker.py.txt').write_bytes(Path(__file__).read_bytes())
    resource = resource_snapshot()
    state['resource'] = resource
    if resource['available_bytes'] < 1536 * 1024**2 or len(resource['lean_processes']) > 2:
        state['status'] = 'NOT_STARTED_RESOURCE_GATE'
        save()
        print(json.dumps(dict(status=state['status'], record=str(record), resource=resource)), flush=True)
        sys.exit(0)
    output = build / ('OddPair130-' + run + '.olean')
    log = attempt / 'compiler.log'
    env = os.environ.copy()
    env['PATH'] = str(BIN) + ';' + env['PATH']
    env['LEAN_PATH'] = ';'.join(environment['paths'])
    cmd = [str(BIN / 'lake.exe'), 'env', 'lean', '-s', '65536', '-R',
           str(HERE / 'lean'), '-o', str(output), str(SOURCE)]
    state.update(status='COMPILING', command=cmd, cwd=str(MATHLIB),
                 log=str(log), object=str(output))
    save()
    print(json.dumps(dict(status='COMPILING', record=str(record), resource=resource)), flush=True)
    start = time.monotonic()
    with log.open('w', encoding='utf-8') as out:
        proc = subprocess.Popen(cmd, cwd=MATHLIB, env=env, stdout=out,
                                stderr=subprocess.STDOUT)
        state['launcher_pid'] = proc.pid
        save()
        try:
            code = proc.wait(timeout=600)
        except subprocess.TimeoutExpired:
            subprocess.run(['taskkill', '/PID', str(proc.pid), '/T', '/F'],
                           stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL, check=False)
            code = proc.wait(timeout=20)
            state['timeout'] = True
    state.update(exit_code=code, seconds=time.monotonic()-start,
                 log_sha256=sha(log), source_current_sha256=sha(SOURCE),
                 checker_current_sha256=sha(__file__))
    text = log.read_text(encoding='utf-8')
    rows = re.findall(r"'([^']+)' depends on axioms:\s*\[([^]]*)\]", text, re.S)
    rows += [(n, '') for n in re.findall(r"'([^']+)' does not depend on any axioms", text)]
    state['axioms'] = [dict(theorem=n, axioms=re.findall(r'[A-Za-z][\w.]*', a)) for n, a in rows]
    if output.exists():
        state['object_sha256'] = sha(output)
    state['dependencies_unchanged'] = all(sha(p) == d for p, d in dependencies.items())
    success = (code == 0 and not state.get('timeout') and 'error:' not in text
               and 'sorryAx' not in text and len(rows) == SOURCE.read_text().count('#print axioms')
               and not re.search(r'\b(sorry|admit|native_decide)\b', SOURCE.read_text())
               and output.exists() and state['source_current_sha256'] == state['source_sha256']
               and state['checker_current_sha256'] == state['checker_sha256']
               and state['dependencies_unchanged']
               and all(set(a['axioms']) <= {'propext', 'Classical.choice', 'Quot.sound'}
                       for a in state['axioms']))
    state['status'] = 'PASS' if success else 'FAILED'
    state['scope'] = 'Actual pair equality requires even length and start; odd length or odd start implies pair>=9, including length235. No new global bound.'
    if success:
        stable = build / 'OddPair130.olean'
        stable.write_bytes(output.read_bytes())
        state['importable_object'] = str(stable)
        state['importable_object_sha256'] = sha(stable)
    save()
    if success:
        (HERE / 'data/independent-odd-pair-audit.json').write_bytes(record.read_bytes())
    print(json.dumps(dict(status=state['status'], seconds=state['seconds'], record=str(record),
                         log=str(log), axioms=state['axioms'])), flush=True)
    sys.exit(0 if success else 1)
except Exception as exc:
    state.update(status='FAILED_BEFORE_OR_AFTER_COMPILE', error=repr(exc))
    save()
    raise
