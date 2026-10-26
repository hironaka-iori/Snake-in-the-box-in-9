"""Replay the dependency graph with three workers; preserve source-checked progress."""
from pathlib import Path
import concurrent.futures,hashlib,json,os,shutil,subprocess,sys,time,uuid,threading
ROOT=Path(__file__).resolve().parents[3];HERE=Path(__file__).resolve().parents[1]
BIN=Path('D:/Codex/2026-10-01/it-should-have-a-property-of/work/lean-research/lean-4.19.0-windows/bin')
build=HERE/'build'/uuid.uuid4().hex;build.mkdir(parents=True);paths=[build]
for prior,tag in [('54-share-coverage','latest'),('52-share-on-235','latest'),('51-exact-bucket-pressure','latest'),('50-three-count-return','latest'),('49-six-direction-pair-catalogue','latest'),('48-low-count-compatibility','latest'),('47-critical-singleton-patterns','latest'),('45-pair-endpoint-demand','latest'),('44-critical-window-generalization','latest'),('42-six-count-state-model','latest'),('41-joint-intervening-sum','latest'),('31-joint-counter-soundness','latest'),('32-seven-count-four-screen','proofs-latest'),('28-direct-share-certificates','latest')]:
 paths.append(Path((ROOT/f'milestones/{prior}/build/{tag}.txt').read_text().strip()))
paths.extend(ROOT/p for p in ['milestones/20-middle-path-release/build','milestones/14-component-construction/build','milestones/07-window-223/lean/generated/geometry/support-ci2y7deg','work/spectral/.verification/strengthened-n8g3mwjy/core/.lake/build/lib/lean','work/spectral/.verification/strengthened-n8g3mwjy'])
env=os.environ.copy();env['PATH']=str(BIN)+';'+env['PATH'];env['LEAN_PATH']=';'.join(map(str,paths))
sources={p.relative_to(HERE/'lean').with_suffix('').as_posix():p for p in (HERE/'lean').rglob('*.lean')}
deps={name:{line.split()[1].replace('.','/') for line in p.read_text(encoding='utf-8-sig').splitlines() if line.startswith('import ')}&sources.keys() for name,p in sources.items()}
records=[];complete=set();lock=threading.Lock()
if '--resume' in sys.argv:
 previous=json.loads((HERE/'logs/build-record.json').read_text());shutil.copytree(previous['build'],build,dirs_exist_ok=True)
 for row in previous['records']:
  source=sources[row['module']]
  if row['exit_code']==0 and row['source_sha256']==hashlib.sha256(source.read_bytes()).hexdigest():records.append(row)
 complete={r['module'] for r in records}
 while True:
  valid={n for n in complete if deps[n]<=complete}
  if valid==complete:break
  complete=valid
 records=[r for r in records if r['module'] in complete]
 for name in set(sources)-complete:
  stale=build/(name+'.olean')
  assert stale.resolve().is_relative_to(build.resolve())
  if stale.exists():stale.unlink()
def run(name):
 source=sources[name];dest=build/(name+'.olean');dest.parent.mkdir(parents=True,exist_ok=True)
 log=HERE/'logs'/(name.replace('/','-')+'.log');t=time.monotonic()
 with log.open('w',encoding='utf-8') as f:
  result=subprocess.run([str(BIN/'lake.exe'),'env','lean','-s','65536','-R',str(HERE/'lean'),'-o',str(dest),str(source)],cwd=BIN.parent.parent/'mathlib',env=env,stdout=f,stderr=subprocess.STDOUT)
 row=dict(module=name,exit_code=result.returncode,seconds=round(time.monotonic()-t,3),source_sha256=hashlib.sha256(source.read_bytes()).hexdigest())
 with lock:
  records.append(row);(HERE/'logs/build-record.json').write_text(json.dumps(dict(build=str(build),records=records),indent=2)+'\n')
 if result.returncode:raise RuntimeError(name+'\n'+log.read_text(encoding='utf-8')[-5000:])
 if '/Data' not in name:print('Built',name,'in',row['seconds'],'s',flush=True)
 return name
pending=set(sources)-complete;running={}
with concurrent.futures.ThreadPoolExecutor(max_workers=3) as pool:
 while pending or running:
  ready=sorted((n for n in pending if deps[n]<=complete),key=lambda n:('/Data' not in n,n))
  for name in ready[:3-len(running)]:pending.remove(name);running[pool.submit(run,name)]=name
  if not running:raise RuntimeError('Unresolved dependencies: '+str(pending))
  done,_=concurrent.futures.wait(running,return_when=concurrent.futures.FIRST_COMPLETED)
  for f in done:complete.add(f.result());running.pop(f)
(HERE/'build/latest.txt').write_text(str(build));print('Completed',len(records),'modules',flush=True)
