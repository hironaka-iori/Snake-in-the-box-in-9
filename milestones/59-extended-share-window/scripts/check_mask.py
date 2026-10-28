"""Replay the dependency graph with three workers; preserve source-checked progress."""
from pathlib import Path
import concurrent.futures,hashlib,json,os,shutil,subprocess,sys,time,uuid,threading
ROOT=Path(__file__).resolve().parents[3];HERE=Path(__file__).resolve().parents[1]
BIN=Path('D:/Codex/2026-10-01/it-should-have-a-property-of/work/lean-research/lean-4.19.0-windows/bin')
build=HERE/'build'/uuid.uuid4().hex;build.mkdir(parents=True);paths=[build,Path((HERE/'build/latest.txt').read_text().strip())]
for prior,tag in [('58-share-pressure','latest'),('54-share-coverage','latest'),('52-share-on-235','latest'),('51-exact-bucket-pressure','latest'),('50-three-count-return','latest'),('49-six-direction-pair-catalogue','latest'),('48-low-count-compatibility','latest'),('47-critical-singleton-patterns','latest'),('45-pair-endpoint-demand','latest'),('44-critical-window-generalization','latest'),('42-six-count-state-model','latest'),('41-joint-intervening-sum','latest'),('31-joint-counter-soundness','latest'),('32-seven-count-four-screen','proofs-latest'),('28-direct-share-certificates','latest')]:
 paths.append(Path((ROOT/f'milestones/{prior}/build/{tag}.txt').read_text().strip()))
paths.extend(ROOT/p for p in ['milestones/20-middle-path-release/build','milestones/14-component-construction/build','milestones/07-window-223/lean/generated/geometry/support-ci2y7deg','work/spectral/.verification/strengthened-n8g3mwjy/core/.lake/build/lib/lean','work/spectral/.verification/strengthened-n8g3mwjy'])
env=os.environ.copy();env['PATH']=str(BIN)+';'+env['PATH'];env['LEAN_PATH']=';'.join(map(str,paths))

import time
out=[]
for name in ['MaskShareBridge','MaskPilot']:
 t=time.monotonic()
 with (HERE/'logs'/f'{name}.log').open('w',encoding='utf-8') as f:
  p=subprocess.run([str(BIN/'lake.exe'),'env','lean','-s','65536','-R',str(HERE/'lean'),'-o',str(build/(name+'.olean')),str(HERE/'lean'/f'{name}.lean')],cwd=BIN.parent.parent/'mathlib',env=env,stdout=f,stderr=subprocess.STDOUT)
 print(name,p.returncode,time.monotonic()-t,flush=True)
 if p.returncode: print((HERE/'logs'/f'{name}.log').read_text());break
 out.append(name)
(HERE/'data/mask-pilot-build.json').write_text(json.dumps(dict(build=str(build),completed=out)))
