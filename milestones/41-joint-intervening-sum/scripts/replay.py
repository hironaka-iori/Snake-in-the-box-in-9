"""Dependency-ordered Lean build; at most two independent check modules run beside data."""
from pathlib import Path
from concurrent.futures import ThreadPoolExecutor
import json,os,re,shutil,subprocess,time,uuid
ROOT=Path(__file__).resolve().parents[3];HERE=Path(__file__).resolve().parents[1]
BIN=Path('D:/Codex/2026-10-01/it-should-have-a-property-of/work/lean-research/lean-4.19.0-windows/bin')
MATHLIB=Path('D:/Codex/2026-10-01/it-should-have-a-property-of/work/lean-research/mathlib')
build=HERE/'build'/uuid.uuid4().hex;build.mkdir(parents=True)
old=Path((HERE/'build/latest.txt').read_text().strip())
shutil.copytree(old,build,dirs_exist_ok=True)
paths=[build]
for prior,tag in [('31-joint-counter-soundness','latest'),('32-seven-count-four-screen','proofs-latest'),('28-direct-share-certificates','latest')]:
 paths.append(Path((ROOT/f'milestones/{prior}/build/{tag}.txt').read_text().strip()))
paths.extend(ROOT/p for p in ['milestones/20-middle-path-release/build','milestones/14-component-construction/build','milestones/07-window-223/lean/generated/geometry/support-ci2y7deg','work/spectral/.verification/strengthened-n8g3mwjy/core/.lake/build/lib/lean','work/spectral/.verification/strengthened-n8g3mwjy'])
env=os.environ.copy();env['PATH']=str(BIN)+';'+env['PATH'];env['LEAN_PATH']=';'.join(map(str,paths))
(HERE/'build/current.json').write_text(json.dumps(dict(pid=os.getpid(),build=str(build)),indent=2))
records=[]
def run(name):
 source=HERE/'lean'/(name+'.lean');dest=build/(name+'.olean');dest.parent.mkdir(parents=True,exist_ok=True)
 if dest.exists():dest.unlink()
 log=HERE/'logs'/(name.replace('/','-')+'.log');t=time.monotonic()
 with log.open('w',encoding='utf-8') as f:
  result=subprocess.run([str(BIN/'lake.exe'),'env','lean','-R',str(HERE/'lean'),'-o',str(dest),str(source)],cwd=MATHLIB,env=env,stdout=f,stderr=subprocess.STDOUT)
 row=dict(module=name,exit_code=result.returncode,seconds=round(time.monotonic()-t,3));records.append(row)
 if result.returncode:
  print(log.read_text(encoding='utf-8')[-4000:],flush=True)
  raise RuntimeError(row)
 print('Built',name,'in',row['seconds'],'s',flush=True)
 return row
try:
 mod='JointIntervening411'
 run('LocalWindowCnf/'+mod);run('LocalWindowSat/'+mod)
 data=sorted((HERE/f'lean/LocalWindowUnsat/{mod}').glob('Data*.lean'),key=lambda p:int(p.stem[4:]))
 checks=sorted((HERE/f'lean/LocalWindowUnsat/{mod}').glob('Check*.lean'),key=lambda p:int(p.stem[5:]))
 needed={p:max(map(int,re.findall(r'\.Data(\d+)',p.read_text()))) for p in checks}
 pending=[];submitted=set()
 with ThreadPoolExecutor(max_workers=2) as pool:
  for p in data:
   run(f'LocalWindowUnsat/{mod}/{p.stem}')
   n=int(p.stem[4:])
   for c in checks:
    if c not in submitted and needed[c]<=n:
     pending.append(pool.submit(run,f'LocalWindowUnsat/{mod}/{c.stem}'));submitted.add(c)
   for f in pending:
    if f.done():f.result()
  for f in pending:f.result()
 run('LocalWindowUnsat/'+mod);run('SumWindow411')
 (HERE/'build/latest.txt').write_text(str(build))
finally:
 (HERE/'logs/build-record.json').write_text(json.dumps(dict(build=str(build),records=records),indent=2)+'\n')
