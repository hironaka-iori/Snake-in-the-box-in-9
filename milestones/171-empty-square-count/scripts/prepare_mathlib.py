from pathlib import Path
import sys,json,hashlib,re
h=Path(__file__).resolve().parents[1];r=h.parents[1];prev=r/'milestones/170-actual-component-closure'
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
m=sys.argv[1];src=h/'lean'/f'{m}.lean';pins={str(h/'scripts/native_resources.py'):sha(h/'scripts/native_resources.py')}
for imp in re.findall(r'^import ([\w.]+)$',src.read_text(encoding='utf-8'),re.M):
    if imp.startswith('Mathlib.'):
        lib=Path(r'D:\Codex\2026-10-01\it-should-have-a-property-of\work\lean-research\mathlib')
        for f in [lib/(imp.replace('.','/')+'.lean'),lib/'.lake/build/lib/lean'/(imp.replace('.','/')+'.olean')]: pins[str(f)]=sha(f)
        continue
    ap=h/'data'/f'{imp}-audit.json'
    if not ap.exists():ap=prev/'data'/f'{imp}-audit.json'
    j=json.loads(ap.read_text());assert j['status']=='PASS'
    for p,d in j['dependencies'].items():assert sha(p)==d,p;pins[p]=d
    for p,d in [(j['source'],j['source_sha256']),(j['object'],j['olean_sha256']),(j['log'],j['log_sha256'])]:assert sha(p)==d,p;pins[p]=d
    pins[str(ap)]=sha(ap)
binpath=Path(r'D:\Codex\2026-10-01\it-should-have-a-property-of\work\lean-research\lean-4.19.0-windows\bin')
pins[str(binpath/'lean.exe')]=sha(binpath/'lean.exe')
j={'new_module_order':[m],'source_sha256':{m:sha(src)},'input_pins':pins,'lean_bin':str(binpath),'search_paths':[str(h/'build'),str(prev/'build'),str(r/'milestones/169-closed-cube-components/build')],'checker_sha256':sha(h/'scripts/check_mathlib.py')}
j['search_paths'] += [x for x in json.loads((r/'milestones/167-undominated-corners/data/local-execution.json').read_text())['search_paths'] if x.startswith('D:')]
(h/'data'/f'{m}-execution.json').write_text(json.dumps(j,indent=2)+'\n')
print('Prepared',m,'with',len(pins),'pinned inputs')
