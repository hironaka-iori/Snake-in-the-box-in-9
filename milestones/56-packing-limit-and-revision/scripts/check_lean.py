from pathlib import Path
import os,subprocess,json,uuid,hashlib
HERE=Path(__file__).resolve().parents[1];ROOT=HERE.parents[1]
BIN=Path('D:/Codex/2026-10-01/it-should-have-a-property-of/work/lean-research/lean-4.19.0-windows/bin')
build=HERE/'build'/uuid.uuid4().hex;build.mkdir(parents=True)
env=os.environ.copy();env['PATH']=str(BIN)+';'+env['PATH']
paths=[build]
for prior in ['50-three-count-return','49-six-direction-pair-catalogue','48-low-count-compatibility','47-critical-singleton-patterns','45-pair-endpoint-demand','44-critical-window-generalization','42-six-count-state-model','41-joint-intervening-sum','31-joint-counter-soundness']:
 paths.append(Path((ROOT/f'milestones/{prior}/build/latest.txt').read_text().strip()))
paths += [ROOT/'milestones/20-middle-path-release/build',ROOT/'milestones/07-window-223/lean/generated/geometry/support-ci2y7deg',ROOT/'work/spectral/.verification/strengthened-n8g3mwjy/core/.lake/build/lib/lean',ROOT/'work/spectral/.verification/strengthened-n8g3mwjy']
env['LEAN_PATH']=';'.join(map(str,paths));records=[]
for source in [HERE/'lean/PackingLimit.lean',HERE/'lean/PaperArithmetic.lean']:
 log=HERE/'logs'/(source.stem+'.log')
 with log.open('w',encoding='utf-8') as out:r=subprocess.run([str(BIN/'lake.exe'),'env','lean','-R',str(HERE/'lean'),'-o',str(build/(source.stem+'.olean')),str(source)],cwd=BIN.parent.parent/'mathlib',env=env,stdout=out,stderr=subprocess.STDOUT)
 print(log.read_text(encoding='utf-8'),flush=True)
 records.append(dict(source=source.name,sha256=hashlib.sha256(source.read_bytes()).hexdigest(),exit_code=r.returncode))
 assert r.returncode==0
(HERE/'data/lean-check.json').write_text(json.dumps(dict(build=str(build),records=records),indent=2)+'\n')
