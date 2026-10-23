"""Export the full-cube witnesses for kernel checks and normalize orientation."""
import hashlib,json
from pathlib import Path
HERE=Path(__file__).resolve().parents[1]
for i,cap in ((0,10),(1,9)):
 p=HERE/f'data/full-{i}-cap-{cap}.json';r=json.loads(p.read_text());assert r['status']=='SAT'
 W=[0]
 for a in r['dirs']:W.append(W[-1]^(1<<a))
 vs=r['vertex_sequence'];start=next((j for j in range(len(vs)-7) if vs[j:j+8]==W),None)
 if start is None:
  vs=vs[::-1];start=next(j for j in range(len(vs)-7) if vs[j:j+8]==W)
 n=len(vs)-1;counts=[r['census']['alpha'][j] for j in (0,5)]
 out=dict(case=i,edges=n,start=start,dirs=r['dirs'],pair_counts=counts,vertex_sequence=vs,source_sha256=hashlib.sha256(p.read_bytes()).hexdigest())
 (HERE/f'data/witness-{i}.json').write_text(json.dumps(out,indent=2)+'\n')
 s=f'''import LocalWindowTags
import LocalWindowBridge

namespace Snake9.PairSharpness.Case{i}
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

theorem window_directions : ∀ j : Fin 7,
    dir witness ({start}+j.val) = ({r['dirs']} : List Nat).getD j.val 0 := by
  simp only [dir, Tags.dirOfStep_eq]
  decide +kernel

theorem pair_counts : coreAlpha witness {start+1} = {counts[0]} ∧
    coreAlpha witness {start+6} = {counts[1]} := by decide +kernel

theorem attains : ∃ p : Snake {n},
    coreAlpha p {start+1} + coreAlpha p {start+6} = {cap} ∧
    (∀ j : Fin 7, dir p ({start}+j.val) = ({r['dirs']} : List Nat).getD j.val 0) := by
  refine ⟨witness, ?_, window_directions⟩
  rw [pair_counts.1,pair_counts.2]

#print axioms distinct
#print axioms induced
#print axioms window_directions
#print axioms pair_counts
#print axioms attains
end Snake9.PairSharpness.Case{i}
'''
 (HERE/f'lean/Witness{i}.lean').write_text(s,encoding='utf-8')
 print('Exported witness',i,'edges',n,'counts',counts,'start',start)
