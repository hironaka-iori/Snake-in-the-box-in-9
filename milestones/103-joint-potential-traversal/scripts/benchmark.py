"""Run matched full-context comparisons sequentially, preserving launch conditions."""
from pathlib import Path
import datetime, hashlib, json, subprocess, sys

HERE = Path(__file__).resolve().parents[1]
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
modules = [
    'CompletedBaseline103D99Q37', 'CompletedJoint103D99Q37',
    'ConditionalJoint103D99Q37', 'ConditionalBaseline103D99Q37',
    'CompletedJoint103D0Q0', 'CompletedBaseline103D0Q0',
    'ConditionalBaseline103D0Q0', 'ConditionalJoint103D0Q0',
]
path = HERE/'data/benchmark-start.json'
assert not path.exists(), 'Launch record is immutable; resume with check.py and the remaining modules.'
command = "@(Get-CimInstance Win32_Process -Filter \"Name='lean.exe'\" | Select-Object ProcessId,PrivatePageCount) | ConvertTo-Json -Compress"
raw = subprocess.check_output(['powershell', '-NoProfile', '-Command', command], text=True).strip()
others = json.loads(raw) if raw else []
assert not others, others
record = dict(started_at=datetime.datetime.now(datetime.timezone.utc).isoformat(),
    order=modules, other_lean_processes=others,
    source_sha256={m: sha(HERE/'lean'/(m+'.lean')) for m in modules},
    checker_sha256=sha(HERE/'scripts/check.py'),
    scope='One sequential pair per profile and context; end-to-end Lean module time, with identical imports, weights, endpoints, acceptance root, slope and clipping bound.')
path.write_text(json.dumps(record, indent=2)+'\n', encoding='utf-8')
subprocess.run([sys.executable, '-B', '-X', 'utf8', str(HERE/'scripts/check.py'), *modules], check=True)
