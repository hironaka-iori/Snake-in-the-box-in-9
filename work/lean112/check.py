import os, subprocess, sys, json, hashlib
from datetime import datetime, timezone
from pathlib import Path
HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[1]
LEAN=ROOT.parent/'Snake in the Box/work/research_20261015/proof/dependencies/lean-4.19.0-windows/bin/lean.exe'
env=os.environ.copy()
env['LEAN_PATH']=';'.join(map(str,[HERE,ROOT/'work/lean/sat-first-checked',ROOT/'work/final_lean/.lake/build/lib/lean']))
OUT=ROOT/'outputs/lean112/bridge-logs'
OUT.mkdir(parents=True,exist_ok=True)
manifest=OUT.parent/'bridge-checks.json'
records=json.loads(manifest.read_text()) if manifest.exists() else {}
for name in sys.argv[1:]:
    src=HERE/(name+'.lean')
    if not src.exists(): src=ROOT/'work/final_lean'/(name+'.lean')
    print('Checking '+name,flush=True)
    log=OUT/(name+'.log')
    with log.open('w',encoding='utf-8') as f:
        result=subprocess.run([str(LEAN),'--root='+str(src.parent),'-o',str(HERE/(name+'.olean')),str(src)],env=env,cwd=ROOT,stdout=f,stderr=subprocess.STDOUT)
    output=log.read_text(encoding='utf-8')
    print(output,end='',flush=True)
    records[name]=dict(exit_code=result.returncode,sha256=hashlib.sha256(src.read_bytes()).hexdigest(),finished_utc=datetime.now(timezone.utc).isoformat())
    if result.returncode==0:
        records[name]['olean_sha256']=hashlib.sha256((HERE/(name+'.olean')).read_bytes()).hexdigest()
    tmp=manifest.with_suffix('.tmp');tmp.write_text(json.dumps(records,indent=2));os.replace(tmp,manifest)
    if result.returncode: sys.exit(result.returncode)
    print('Passed '+name,flush=True)
