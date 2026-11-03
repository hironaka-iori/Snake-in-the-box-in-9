"""One resource-gated isolated Lean attempt; preserves each source and run record."""
from pathlib import Path
import hashlib, json, os, re, subprocess, sys, time

HERE = Path(__file__).resolve().parents[1]
BIN = Path('D:/Codex/2026-10-01/it-should-have-a-property-of/work/lean-research/lean-4.19.0-windows/bin')
MATHLIB = BIN.parent.parent / 'mathlib'
SOURCE = HERE / 'lean/DirectCardinality127.lean'
sha = lambda p: hashlib.sha256(Path(p).read_bytes()).hexdigest()
run = str(time.time_ns())
attempt = HERE / 'logs' / ('direct-cardinality-' + run)
attempt.mkdir(parents=True)
build = HERE / 'build-independent'
build.mkdir(exist_ok=True)
record = attempt / 'record.json'

command = "$osInfo = Get-CimInstance Win32_OperatingSystem; $leanProcesses = @(Get-CimInstance Win32_Process -Filter \"Name='lean.exe'\" | Select-Object ProcessId,PrivatePageCount); @{available_bytes=([long]$osInfo.FreePhysicalMemory*1024); lean_processes=$leanProcesses} | ConvertTo-Json -Depth 3 -Compress"
resource = json.loads(subprocess.check_output(
    ['powershell', '-NoProfile', '-Command', command], text=True))
state = dict(status='NOT_STARTED', resource=resource,
             source_sha256=sha(SOURCE), checker_sha256=sha(__file__),
             started_at_ns=time.time_ns(), pid=os.getpid())

def save():
    record.write_text(json.dumps(state, indent=2) + '\n', encoding='utf-8')

if resource['available_bytes'] < 1536 * 1024**2 or len(resource['lean_processes']) > 2:
    state['status'] = 'NOT_STARTED_RESOURCE_GATE'
    save()
    print(json.dumps(state), flush=True)
    sys.exit(0)

dependencies = {}
for name in ['Mathlib.Data.Finset.Powerset', 'Mathlib.Data.Fintype.Card']:
    rel = Path(*name.split('.'))
    for path in [MATHLIB / rel.with_suffix('.lean'),
                 MATHLIB / '.lake/build/lib/lean' / rel.with_suffix('.olean')]:
        dependencies[str(path)] = sha(path)
rel = Path('Lean/Elab/Tactic/Omega')
for path in [BIN.parent / 'src/lean' / rel.with_suffix('.lean'),
             BIN.parent / 'lib/lean' / rel.with_suffix('.olean'),
             MATHLIB / 'lake-manifest.json', MATHLIB / 'lean-toolchain',
             BIN / 'lean.exe', BIN / 'lake.exe']:
    dependencies[str(path)] = sha(path)
state['dependencies'] = dependencies
(attempt / 'source.lean.txt').write_bytes(SOURCE.read_bytes())
(attempt / 'checker.py.txt').write_bytes(Path(__file__).read_bytes())
output = build / ('DirectCardinality127-' + run + '.olean')
log = attempt / 'compiler.log'
env = os.environ.copy()
env['PATH'] = str(BIN) + ';' + env['PATH']
env.pop('LEAN_PATH', None)
cmd = [str(BIN / 'lake.exe'), 'env', 'lean', '-s', '65536', '-R',
       str(HERE / 'lean'), '-o', str(output), str(SOURCE)]
state.update(status='COMPILING', command=cmd, cwd=str(MATHLIB),
             log=str(log), object=str(output))
save()
print(json.dumps(dict(status='COMPILING', record=str(record),
                     resource=resource)), flush=True)
start = time.monotonic()
with log.open('w', encoding='utf-8') as out:
    proc = subprocess.Popen(cmd, cwd=MATHLIB, env=env, stdout=out,
                            stderr=subprocess.STDOUT)
    state['launcher_pid'] = proc.pid
    save()
    try:
        code = proc.wait(timeout=90)
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
           and 'sorryAx' not in text and len(rows) == 5 and output.exists()
           and state['source_current_sha256'] == state['source_sha256']
           and state['checker_current_sha256'] == state['checker_sha256']
           and state['dependencies_unchanged']
           and all(set(a['axioms']) <= {'propext', 'Classical.choice', 'Quot.sound'}
                   for a in state['axioms']))
state['status'] = 'PASS' if success else 'FAILED'
state['scope'] = 'Generic finite-cardinality statements only; no concrete RUP or snake refutation.'
save()
print(json.dumps(state), flush=True)
sys.exit(0 if success else 1)
