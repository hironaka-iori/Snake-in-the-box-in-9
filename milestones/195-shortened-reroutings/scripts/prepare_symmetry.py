from pathlib import Path
import hashlib,json
H=Path(__file__).resolve().parents[1]
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
module='Symmetry195'
plan=dict(new_module_order=[module],source_sha256={module:sha(H/'lean'/(module+'.lean'))},input_pins={str(H/'scripts/native_resources.py'):sha(H/'scripts/native_resources.py')},
 lean_bin='D:/Codex/2026-10-01/it-should-have-a-property-of/work/lean-research/lean-4.19.0-windows/bin',search_paths=[str(H/'build')],checker_sha256=sha(H/'scripts/check_core.py'))
target=H/'data'/(module+'-execution.json');assert not target.exists();target.write_text(json.dumps(plan,indent=2)+'\n')
