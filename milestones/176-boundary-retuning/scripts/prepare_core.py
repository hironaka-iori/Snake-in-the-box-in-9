from pathlib import Path
import sys,json,hashlib
h=Path(__file__).resolve().parents[1];m=sys.argv[1];sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
b=Path(r'D:\Codex\2026-10-01\it-should-have-a-property-of\work\lean-research\lean-4.19.0-windows\bin')
s=h/'lean'/f'{m}.lean';pins={str(b/'lean.exe'):sha(b/'lean.exe'),str(h/'scripts/native_resources.py'):sha(h/'scripts/native_resources.py')}
j={'new_module_order':[m],'source_sha256':{m:sha(s)},'input_pins':pins,'lean_bin':str(b),'search_paths':[str(h/'build')],'checker_sha256':sha(h/'scripts/check_core.py')}
(h/'data'/f'{m}-execution.json').write_text(json.dumps(j,indent=2)+'\n',encoding='utf-8')
print('Prepared core',m)
