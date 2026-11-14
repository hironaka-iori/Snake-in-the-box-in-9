from pathlib import Path
import datetime,hashlib,json,subprocess
from native_resources import snapshot
H=Path(__file__).resolve().parents[1]
compiler=Path('D:/Codex/2026-10-01/it-should-have-a-property-of/work/lean-research/lean-4.19.0-windows/bin/leanc.exe')
source=H/'scripts/tight_solver.c';binary=H/'build/tight_solver.exe'
gate=snapshot()
assert not gate['errors'] and not gate['processes'] and gate['free_bytes']>=1024**3,gate
assert not (H/'data/history-search.lock').exists()
cmd=[str(compiler),'-O2','-std=c11','-Wall','-Wextra',str(source),'-o',str(binary)]
run=subprocess.run(cmd,stdout=subprocess.PIPE,stderr=subprocess.PIPE,timeout=60)
(H/'logs/tight-compiler.stdout').write_bytes(run.stdout)
(H/'logs/tight-compiler.stderr').write_bytes(run.stderr)
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
receipt={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'command':cmd,'resource_gate':gate,
'exit_code':run.returncode,'source_sha256':sha(source),'compiler_sha256':sha(compiler),
'binary_sha256':sha(binary) if binary.exists() else None}
(H/'data/tight-compiler-receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
print(json.dumps(receipt,indent=2))
assert run.returncode==0,run.stderr.decode()
