"""Generate and check a complete snake attaining the four-step return bound."""
from pathlib import Path
import json,subprocess,hashlib,time
HERE=Path(__file__).resolve().parents[1];ROOT=HERE.parents[1]
s=(ROOT/'milestones/44-critical-window-generalization/scripts/witnesses.py').read_text()
s=s[:s.index('# The optimum')].replace("specs=[('Sharp','full-sharp-seven',7),('Short','full-short-six',6)]", "specs=[('Return','full-return-five',5)]").replace('Snake9.ExteriorTurn','Snake9.FourStepReturn')
exec(compile(s,'witness_template','exec'),globals())
r=json.loads((HERE/'data/witness-return.json').read_text());start=r['start'];vs=r['vertex_sequence']
assert len(set(vs))==147
assert all(((vs[i]^vs[j]).bit_count()==1)==(j==i+1) for i in range(len(vs)) for j in range(i+1,len(vs)))
s=f'''import SumWindow4934
import WitnessReturn
namespace Snake9.FourStepReturn
open Snake9.LocalWindow

theorem sharp_constant (K : Nat)
    (h : ∀ {{m : Nat}} (p : Snake m) (r : Nat), r+4 ≤ m →
      (∀ j, j<4 → dir p (r+j) = ([0,1,2,0] : List Nat).getD j 0) →
      K ≤ coreAlpha p (r+1)+coreAlpha p (r+3)) : K ≤ 5 := by
  have hb := h Return.witness {start} (by decide)
    (by intro j hj; exact Return.window_directions ⟨j,hj⟩)
  norm_num only at hb
  rw [Return.pair_counts.1,Return.pair_counts.2] at hb
  exact hb
#print axioms sharp_constant
end Snake9.FourStepReturn
'''
(HERE/'lean/ReturnSharpConstant.lean').write_text(s,encoding='utf-8')
prefix=(HERE/'scripts/return_replay.py').read_text(encoding='utf-8-sig');exec(prefix[:prefix.index("mod='JointIntervening4934'")],globals())
records=[]
for name in ['WitnessReturn','ReturnSharpConstant']:
 source=HERE/f'lean/{name}.lean';dest=build/(name+'.olean');log=HERE/f'logs/{name}.log';t=time.monotonic()
 with log.open('w',encoding='utf-8') as f:
  result=subprocess.run([str(BIN/'lake.exe'),'env','lean','-R',str(HERE/'lean'),'-o',str(dest),str(source)],cwd=BIN.parent.parent/'mathlib',env=env,stdout=f,stderr=subprocess.STDOUT)
 records.append(dict(module=name,exit_code=result.returncode,seconds=round(time.monotonic()-t,3),source_sha256=hashlib.sha256(source.read_bytes()).hexdigest()))
 (HERE/'logs/witness-build-record.json').write_text(json.dumps(dict(build=str(build),records=records),indent=2)+'\n')
 if result.returncode:raise RuntimeError(log.read_text(encoding='utf-8'))
 print('Built',name,'in',records[-1]['seconds'],'s',flush=True)
