"""Early checks of each late clause family, before the full instance pass."""
import hashlib,json,os,pathlib,subprocess,sys,time
from resource_limits import run_bounded
from generate_bridge import emit
ROOT=pathlib.Path(__file__).resolve().parents[2];OUT=ROOT/'outputs/window244';CACHE=OUT/'cache';LOG=OUT/'logs'
LEAN=ROOT.parent/'Snake in the Box/work/research_20261015/proof/dependencies/lean-4.19.0-windows/bin/lean.exe'
MATHLIB=LEAN.parents[2]/'mathlib4'
FOUNDATION=ROOT.parent/'Snake in the Box/work/spectral/.verification/strengthened-n0xmejea'
env=os.environ.copy();env['LEAN_PATH']=os.pathsep.join(map(str,[CACHE,FOUNDATION,FOUNDATION/'core/.lake/build/lib/lean']))
env['LEAN_PATH']=subprocess.check_output([str(LEAN.with_name('lake.exe')),'-d',str(MATHLIB),'env',sys.executable,'-c',"import os;print(os.environ['LEAN_PATH'])"],env=env,text=True).strip()
emit('repeated')
records={}
for block in [27,36,40,48]:
    name=f'W223RepeatedGeometryBlock{block:03d}Part0';src=ROOT/'work/window244/generated'/(name+'.lean');log=LOG/(name+'.smoke.log')
    start=time.monotonic()
    with log.open('w',encoding='utf-8') as f:
        r=run_bounded([str(LEAN),'-j','1','--root='+str(src.parent),'-o',str(CACHE/(name+'.olean')),str(src)],f,cwd=ROOT,env=env)
    r.update(seconds=time.monotonic()-start,source_sha256=hashlib.sha256(src.read_bytes()).hexdigest(),log_sha256=hashlib.sha256(log.read_bytes()).hexdigest())
    records[name]=r;(OUT/'geometry-family-smoke.json').write_text(json.dumps(records,indent=2)+'\n')
    print(name,r['exit_code'],round(r['seconds'],2),flush=True)
    if r['exit_code']:print(log.read_text(encoding='utf-8')[-4000:]);raise SystemExit(1)
