"""Build the pair-count proof in dependency order against pinned local support."""
from pathlib import Path
import hashlib,json,os,re,subprocess,time,uuid
ROOT=Path(__file__).resolve().parents[3];HERE=Path(__file__).resolve().parents[1]
BIN=Path('D:/Codex/2026-10-01/it-should-have-a-property-of/work/lean-research/lean-4.19.0-windows/bin')
MATHLIB=BIN.parent.parent/'mathlib'
build=HERE/'build'/uuid.uuid4().hex;build.mkdir(parents=True)
paths=[build]
for prior,tag in [('41-joint-intervening-sum','latest'),('31-joint-counter-soundness','latest'),('32-seven-count-four-screen','proofs-latest'),('28-direct-share-certificates','latest')]:
    paths.append(Path((ROOT/f'milestones/{prior}/build/{tag}.txt').read_text().strip()))
paths.extend(ROOT/p for p in ['milestones/20-middle-path-release/build','milestones/14-component-construction/build','milestones/07-window-223/lean/generated/geometry/support-ci2y7deg','work/spectral/.verification/strengthened-n8g3mwjy/core/.lake/build/lib/lean','work/spectral/.verification/strengthened-n8g3mwjy'])
env=os.environ.copy();env['PATH']=str(BIN)+';'+env['PATH'];env['LEAN_PATH']=';'.join(map(str,paths))
records=[]
mod='JointIntervening441'
names=['LocalWindowCnf/'+mod,'LocalWindowSat/'+mod]
names += [f'LocalWindowUnsat/{mod}/'+p.stem for p in sorted((HERE/f'lean/LocalWindowUnsat/{mod}').glob('Data*.lean'),key=lambda p:int(p.stem[4:]))]
names += [f'LocalWindowUnsat/{mod}/'+p.stem for p in sorted((HERE/f'lean/LocalWindowUnsat/{mod}').glob('Check*.lean'),key=lambda p:int(p.stem[5:]))]
names += ['LocalWindowUnsat/'+mod,'SumWindow441']
try:
    for name in names:
        source=HERE/'lean'/(name+'.lean');dest=build/(name+'.olean');dest.parent.mkdir(parents=True,exist_ok=True)
        log=HERE/'logs'/(name.replace('/','-')+'.log');t=time.monotonic()
        with log.open('w',encoding='utf-8') as f:
            result=subprocess.run([str(BIN/'lake.exe'),'env','lean','-R',str(HERE/'lean'),'-o',str(dest),str(source)],cwd=MATHLIB,env=env,stdout=f,stderr=subprocess.STDOUT)
        row=dict(module=name,exit_code=result.returncode,seconds=round(time.monotonic()-t,3),source_sha256=hashlib.sha256(source.read_bytes()).hexdigest());records.append(row)
        if result.returncode:
            print(log.read_text()[-5000:],flush=True);raise RuntimeError(row)
        print('Built',name,'in',row['seconds'],'s',flush=True)
    (HERE/'build/latest.txt').write_text(str(build))
finally:
    (HERE/'logs/build-record.json').write_text(json.dumps(dict(build=str(build),records=records),indent=2)+'\n')
