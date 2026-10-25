"""Replay independent certificate chains with two workers and source-checked resume."""
from pathlib import Path
import concurrent.futures,hashlib,json,os,shutil,subprocess,sys,time,uuid,threading
ROOT=Path(__file__).resolve().parents[3];HERE=Path(__file__).resolve().parents[1]
BIN=Path('D:/Codex/2026-10-01/it-should-have-a-property-of/work/lean-research/lean-4.19.0-windows/bin')
build=HERE/'build'/uuid.uuid4().hex;build.mkdir(parents=True);paths=[build]
for prior,tag in [('48-low-count-compatibility','latest'),('47-critical-singleton-patterns','latest'),('45-pair-endpoint-demand','latest'),('44-critical-window-generalization','latest'),('41-joint-intervening-sum','latest'),('31-joint-counter-soundness','latest'),('32-seven-count-four-screen','proofs-latest'),('28-direct-share-certificates','latest')]:
 paths.append(Path((ROOT/f'milestones/{prior}/build/{tag}.txt').read_text().strip()))
paths.extend(ROOT/p for p in ['milestones/20-middle-path-release/build','milestones/14-component-construction/build','milestones/07-window-223/lean/generated/geometry/support-ci2y7deg','work/spectral/.verification/strengthened-n8g3mwjy/core/.lake/build/lib/lean','work/spectral/.verification/strengthened-n8g3mwjy'])
env=os.environ.copy();env['PATH']=str(BIN)+';'+env['PATH'];env['LEAN_PATH']=';'.join(map(str,paths))
records=[];lock=threading.Lock();complete=set()
if '--resume' in sys.argv:
 previous=json.loads((HERE/'logs/build-record.json').read_text());shutil.copytree(previous['build'],build,dirs_exist_ok=True)
 for row in previous['records']:
  source=HERE/'lean'/(row['module']+'.lean')
  if row['exit_code']==0 and source.exists() and row['source_sha256']==hashlib.sha256(source.read_bytes()).hexdigest():records.append(row)
 complete={r['module'] for r in records}
def run(name):
 if name in complete:return
 source=HERE/'lean'/(name+'.lean');dest=build/(name+'.olean');dest.parent.mkdir(parents=True,exist_ok=True)
 log=HERE/'logs'/(name.replace('/','-')+'.log');t=time.monotonic()
 with log.open('w',encoding='utf-8') as f:
  result=subprocess.run([str(BIN/'lake.exe'),'env','lean','-R',str(HERE/'lean'),'-o',str(dest),str(source)],cwd=BIN.parent.parent/'mathlib',env=env,stdout=f,stderr=subprocess.STDOUT)
 row=dict(module=name,exit_code=result.returncode,seconds=round(time.monotonic()-t,3),source_sha256=hashlib.sha256(source.read_bytes()).hexdigest())
 with lock:
  records.append(row);(HERE/'logs/build-record.json').write_text(json.dumps(dict(build=str(build),records=records),indent=2)+'\n')
 if result.returncode:raise RuntimeError(name+'\n'+log.read_text(encoding='utf-8')[-4000:])
 if name.startswith(('PairBasis','CycleExclusion')):print('Built',name,'in',row['seconds'],'s',flush=True)
def chain(number):
 # Wait only for the specific certificate generation output; generation runs in its own live session.
 deadline=time.monotonic()+1800
 while not (HERE/f'logs/cycle{number}-export.txt').exists():
  if time.monotonic()>deadline:raise RuntimeError(f'Certificate {number} not generated')
  time.sleep(1)
 mod=f'CycleWindow{number}';names=['LocalWindowCnf/'+mod,'LocalWindowSat/'+mod]
 for prefix in ['Data','Check']:
  names += [f'LocalWindowUnsat/{mod}/'+p.stem for p in sorted((HERE/f'lean/LocalWindowUnsat/{mod}').glob(prefix+'*.lean'),key=lambda p:int(p.stem[len(prefix):]))]
 names+=['LocalWindowUnsat/'+mod,f'CycleExclusion{number}',f'PairBasis{number}']
 for name in names:run(name)
with concurrent.futures.ThreadPoolExecutor(max_workers=2) as pool:
 futures=[pool.submit(chain,r['number']) for r in json.loads((HERE/'data/cases.json').read_text())]
 for future in concurrent.futures.as_completed(futures):future.result()
if (HERE/'lean/SurveyCatalogue.lean').exists():run('SurveyCatalogue')
(HERE/'build/latest.txt').write_text(str(build))
print('Completed',len(records),'modules',flush=True)
