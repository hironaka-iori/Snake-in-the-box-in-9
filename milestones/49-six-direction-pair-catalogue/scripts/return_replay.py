"""Check the stronger four-step sum in the active build, with a separate receipt."""
from pathlib import Path
import hashlib,json,os,subprocess,time
ROOT=Path(__file__).resolve().parents[3];HERE=Path(__file__).resolve().parents[1]
BIN=Path('D:/Codex/2026-10-01/it-should-have-a-property-of/work/lean-research/lean-4.19.0-windows/bin')
build=Path(json.loads((HERE/'logs/build-record.json').read_text())['build']);paths=[build]
for prior,tag in [('48-low-count-compatibility','latest'),('47-critical-singleton-patterns','latest'),('45-pair-endpoint-demand','latest'),('44-critical-window-generalization','latest'),('41-joint-intervening-sum','latest'),('31-joint-counter-soundness','latest'),('32-seven-count-four-screen','proofs-latest'),('28-direct-share-certificates','latest')]:
 paths.append(Path((ROOT/f'milestones/{prior}/build/{tag}.txt').read_text().strip()))
paths.extend(ROOT/p for p in ['milestones/20-middle-path-release/build','milestones/14-component-construction/build','milestones/07-window-223/lean/generated/geometry/support-ci2y7deg','work/spectral/.verification/strengthened-n8g3mwjy/core/.lake/build/lib/lean','work/spectral/.verification/strengthened-n8g3mwjy'])
env=os.environ.copy();env['PATH']=str(BIN)+';'+env['PATH'];env['LEAN_PATH']=';'.join(map(str,paths))
mod='JointIntervening4934';names=['LocalWindowCnf/'+mod,'LocalWindowSat/'+mod]
for prefix in ['Data','Check']:
 names += [f'LocalWindowUnsat/{mod}/'+p.stem for p in sorted((HERE/f'lean/LocalWindowUnsat/{mod}').glob(prefix+'*.lean'),key=lambda p:int(p.stem[len(prefix):]))]
names+=['LocalWindowUnsat/'+mod,'SumWindow4934'];records=[]
for name in names:
 source=HERE/'lean'/(name+'.lean');dest=build/(name+'.olean');dest.parent.mkdir(parents=True,exist_ok=True)
 log=HERE/'logs'/(name.replace('/','-')+'.log');t=time.monotonic()
 with log.open('w',encoding='utf-8') as f:
  result=subprocess.run([str(BIN/'lake.exe'),'env','lean','-R',str(HERE/'lean'),'-o',str(dest),str(source)],cwd=BIN.parent.parent/'mathlib',env=env,stdout=f,stderr=subprocess.STDOUT)
 records.append(dict(module=name,exit_code=result.returncode,seconds=round(time.monotonic()-t,3),source_sha256=hashlib.sha256(source.read_bytes()).hexdigest()))
 (HERE/'logs/return-build-record.json').write_text(json.dumps(dict(build=str(build),records=records),indent=2)+'\n')
 if result.returncode:raise RuntimeError(log.read_text(encoding='utf-8'))
 print('Built',name,flush=True)
