"""Export complete sharpness and shorter-context witnesses for kernel checking."""
from pathlib import Path
import hashlib,json,os,shutil,subprocess,time,uuid
ROOT=Path(__file__).resolve().parents[3];HERE=Path(__file__).resolve().parents[1]
specs=[('Sharp','full-sharp-seven',7),('Short','full-short-six',6)]
for tag,name,total in specs:
    file=HERE/f'data/{name}.json';r=json.loads(file.read_text());assert r['status']=='SAT'
    vs=r['vertex_sequence'];n=len(vs)-1;start=r['window_start'];ds=r['directions'];positions=r['positions']
    counts=[r['census']['alpha'][j-1] for j in positions]
    assert sum(counts)==total and start+len(ds)<=n
    a,b=[start+j for j in positions]
    out=dict(edges=n,start=start,directions=ds,positions=positions,pair_counts=counts,vertex_sequence=vs,source_sha256=hashlib.sha256(file.read_bytes()).hexdigest())
    (HERE/f'data/witness-{tag.lower()}.json').write_text(json.dumps(out,indent=2)+'\n')
    source=f'''import LocalWindowTags
import LocalWindowBridge

namespace Snake9.ExteriorTurn.{tag}
open Snake9.LocalWindow
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

def values : Array Nat := #[{', '.join(map(str,vs))}]
def vertex (i : Fin {n+1}) : Vertex :=
  ⟨values[i.val]! % 512, Nat.mod_lt _ (by decide)⟩
theorem distinct : ∀ i j : Fin {n+1}, vertex i = vertex j → i = j := by decide +kernel
theorem induced : ∀ i j : Fin {n+1}, i.val < j.val →
    (Adj (vertex i) (vertex j) ↔ i.val+1=j.val) := by decide +kernel
def witness : Snake {n} := ⟨vertex, distinct, induced⟩
theorem window_directions : ∀ j : Fin {len(ds)},
    dir witness ({start}+j.val) = ({ds} : List Nat).getD j.val 0 := by
  simp only [dir, Tags.dirOfStep_eq]
  decide +kernel
theorem pair_counts : coreAlpha witness {a} = {counts[0]} ∧
    coreAlpha witness {b} = {counts[1]} := by decide +kernel
theorem attains : ∃ p : Snake {n},
    coreAlpha p {a} + coreAlpha p {b} = {total} ∧
    (∀ j : Fin {len(ds)}, dir p ({start}+j.val) = ({ds} : List Nat).getD j.val 0) := by
  refine ⟨witness, ?_, window_directions⟩
  rw [pair_counts.1,pair_counts.2]

#print axioms distinct
#print axioms induced
#print axioms window_directions
#print axioms pair_counts
#print axioms attains
end Snake9.ExteriorTurn.{tag}
'''
    (HERE/f'lean/Witness{tag}.lean').write_text(source,encoding='utf-8')

# The optimum is for the pattern inequality, not for the longest Q9 snake.
r=json.loads((HERE/'data/witness-sharp.json').read_text());start=r['start'];n=r['edges']
source=f'''import SumWindow441
import WitnessSharp
import WitnessShort

namespace Snake9.ExteriorTurn
open Snake9.LocalWindow
theorem sharp_constant (K : Nat)
    (h : ∀ {{m : Nat}} (p : Snake m) (r : Nat), r+8 ≤ m →
      (∀ j, j<8 → dir p (r+j) = ([0,1,2,3,4,0,3,1] : List Nat).getD j 0) →
      K ≤ coreAlpha p (r+2)+coreAlpha p (r+6)) : K ≤ 7 := by
  have hb := h Sharp.witness {start} (by decide)
    (by intro j hj; exact Sharp.window_directions ⟨j,hj⟩)
  norm_num only at hb
  rw [Sharp.pair_counts.1,Sharp.pair_counts.2] at hb
  exact hb

theorem shorter_claim_false : ¬ (∀ {{m : Nat}} (p : Snake m) (r : Nat), r+6 ≤ m →
    (∀ j, j<6 → dir p (r+j) = ([0,1,2,3,4,2] : List Nat).getD j 0) →
    7 ≤ coreAlpha p (r+1)+coreAlpha p (r+5)) := by
  intro h
'''
q=json.loads((HERE/'data/witness-short.json').read_text())
source+=f'''  have hb := h Short.witness {q['start']} (by decide)
    (by intro j hj; exact Short.window_directions ⟨j,hj⟩)
  norm_num only at hb
  rw [Short.pair_counts.1,Short.pair_counts.2] at hb
  omega

#print axioms sharp_constant
#print axioms shorter_claim_false
end Snake9.ExteriorTurn
'''
(HERE/'lean/SharpConstant.lean').write_text(source,encoding='utf-8')

BIN=Path('D:/Codex/2026-10-01/it-should-have-a-property-of/work/lean-research/lean-4.19.0-windows/bin')
MATHLIB=BIN.parent.parent/'mathlib'
old=Path((HERE/'build/latest.txt').read_text().strip())
build=HERE/'build'/uuid.uuid4().hex;shutil.copytree(old,build)
paths=[build]
for prior,tag in [('41-joint-intervening-sum','latest'),('31-joint-counter-soundness','latest'),('32-seven-count-four-screen','proofs-latest'),('28-direct-share-certificates','latest')]:
    paths.append(Path((ROOT/f'milestones/{prior}/build/{tag}.txt').read_text().strip()))
paths.extend(ROOT/p for p in ['milestones/20-middle-path-release/build','milestones/14-component-construction/build','milestones/07-window-223/lean/generated/geometry/support-ci2y7deg','work/spectral/.verification/strengthened-n8g3mwjy/core/.lake/build/lib/lean','work/spectral/.verification/strengthened-n8g3mwjy'])
env=os.environ.copy();env['PATH']=str(BIN)+';'+env['PATH'];env['LEAN_PATH']=';'.join(map(str,paths))
records=[]
try:
    for name in ['WitnessSharp','WitnessShort','SharpConstant']:
        source=HERE/f'lean/{name}.lean';dest=build/(name+'.olean');log=HERE/f'logs/{name}.log';t=time.monotonic()
        with log.open('w',encoding='utf-8') as f:
            result=subprocess.run([str(BIN/'lake.exe'),'env','lean','-R',str(HERE/'lean'),'-o',str(dest),str(source)],cwd=MATHLIB,env=env,stdout=f,stderr=subprocess.STDOUT)
        records.append(dict(module=name,exit_code=result.returncode,seconds=round(time.monotonic()-t,3),source_sha256=hashlib.sha256(source.read_bytes()).hexdigest()))
        if result.returncode:print(log.read_text()[-6000:],flush=True);raise RuntimeError(name)
        print('Built',name,'in',records[-1]['seconds'],'s',flush=True)
    (HERE/'build/latest.txt').write_text(str(build))
finally:
    (HERE/'logs/witness-build-record.json').write_text(json.dumps(dict(build=str(build),records=records),indent=2)+'\n')
