from pathlib import Path
import sys,json,hashlib,re
h=Path(__file__).resolve().parents[1];r=h.parents[1];sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
m=sys.argv[1];src=h/'lean'/f'{m}.lean';pins={str(h/'scripts/native_resources.py'):sha(h/'scripts/native_resources.py')}
legacy=json.loads((r/'milestones/73-countfree-share-catalogue/bridge/logs/build-record.json').read_text());oldpaths=list(map(Path,legacy['paths']));recent=[r/f'milestones/{x}/build' for x in ['172-share-loss-integration','171-empty-square-count','170-actual-component-closure','169-closed-cube-components']]
for imp in re.findall(r'^import ([\w.]+)$',src.read_text(encoding='utf-8'),re.M):
    if imp=='ShareCharge':
        audit=r/'milestones/73-countfree-share-catalogue/bridge/data/proof-audit.json';j=json.loads(audit.read_text());row=next(x for x in j['newly_checked_modules'] if x['module']=='ShareCharge');sp=r/'milestones/73-countfree-share-catalogue/bridge/upstream/ShareCharge.lean';op=oldpaths[0]/'ShareCharge.olean';assert sha(sp)==row['source_sha256'] and sha(op)==row['olean_sha256'];pins[str(audit)]=sha(audit);pins[str(sp)]=sha(sp)
        core=r/'work/spectral/.verification/strengthened-n8g3mwjy/core';oldroot=core.parent
        for name in ['Snake9','PathStructure','CubeLocal','SingletonSquareLemma','SquareIncidence','ShareCharge']:
            p=next(d/(name+'.olean') for d in oldpaths if (d/(name+'.olean')).exists());pins[str(p)]=sha(p)
            sp=core/(name+'.lean') if (core/(name+'.lean')).exists() else oldroot/(name+'.lean')
            if sp.exists():pins[str(sp)]=sha(sp)
        continue
    if imp.startswith('Mathlib.'):continue
    choices=[h/'data'/f'{imp}-audit.json']+[x.parent/'data'/f'{imp}-audit.json' for x in recent];ap=next(p for p in choices if p.exists());j=json.loads(ap.read_text());assert j['status']=='PASS'
    for p,d in j['dependencies'].items():assert sha(p)==d,p;pins[p]=d
    for p,d in [(j['source'],j['source_sha256']),(j['object'],j['olean_sha256']),(j['log'],j['log_sha256'])]:assert sha(p)==d,p;pins[p]=d
    pins[str(ap)]=sha(ap)
b=Path(r'D:\Codex\2026-10-01\it-should-have-a-property-of\work\lean-research\lean-4.19.0-windows\bin');pins[str(b/'lean.exe')]=sha(b/'lean.exe')
libpaths=[x for x in json.loads((r/'milestones/167-undominated-corners/data/local-execution.json').read_text())['search_paths'] if x.startswith('D:')]
j={'new_module_order':[m],'source_sha256':{m:sha(src)},'input_pins':pins,'lean_bin':str(b),'search_paths':[str(h/'build')]+list(map(str,oldpaths))+list(map(str,recent))+libpaths,'checker_sha256':sha(h/'scripts/check_mathlib.py')}
(h/'data'/f'{m}-execution.json').write_text(json.dumps(j,indent=2)+'\n');print('Prepared',m,len(pins),'pins')
