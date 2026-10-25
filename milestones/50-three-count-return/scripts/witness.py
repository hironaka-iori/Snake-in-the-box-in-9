"""Generate a complete triple-sum sharpness witness and its optimal-constant statement."""
from pathlib import Path
import json,hashlib
HERE=Path(__file__).resolve().parents[1]
r=json.loads((HERE/'data/full-triple-thirteen.json').read_text());vs=r['vertex_sequence'];n=len(vs)-1;start=r['window_start'];pos=[1,4,5];indices=[start+j for j in pos];counts=[r['census']['alpha'][j-1] for j in pos]
assert n==143 and sum(counts)==13
(HERE/'data/witness.json').write_text(json.dumps(dict(edges=n,start=start,indices=indices,counts=counts,vertex_sequence=vs,source_sha256=hashlib.sha256((HERE/'data/full-triple-thirteen.json').read_bytes()).hexdigest()),indent=2)+'\n')
s=f'''import LocalWindowTags
import LocalWindowBridge
import Mathlib.Tactic
namespace Snake9.TripleReturn
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
theorem window_directions : ∀ j : Fin 6,
    dir witness ({start}+j.val) = ([0,1,2,3,4,0] : List Nat).getD j.val 0 := by
  simp only [dir, Tags.dirOfStep_eq]
  decide +kernel
theorem triple_counts : coreAlpha witness {indices[0]} = {counts[0]} ∧
    coreAlpha witness {indices[1]} = {counts[1]} ∧ coreAlpha witness {indices[2]} = {counts[2]} := by decide +kernel

theorem attains : ∃ p : Snake {n},
    coreAlpha p {indices[0]} + coreAlpha p {indices[1]} + coreAlpha p {indices[2]} = 13 ∧
    (∀ j : Fin 6, dir p ({start}+j.val) = ([0,1,2,3,4,0] : List Nat).getD j.val 0) := by
  refine ⟨witness, ?_, window_directions⟩
  rw [triple_counts.1,triple_counts.2.1,triple_counts.2.2]

theorem sharp_constant (K : Nat)
    (h : ∀ {{m : Nat}} (p : Snake m) (r : Nat), r+6 ≤ m →
      (∀ j, j<6 → dir p (r+j) = ([0,1,2,3,4,0] : List Nat).getD j 0) →
      K ≤ coreAlpha p (r+1)+coreAlpha p (r+4)+coreAlpha p (r+5)) : K ≤ 13 := by
  have hb := h witness {start} (by decide)
    (by intro j hj; exact window_directions ⟨j,hj⟩)
  norm_num only at hb
  rw [triple_counts.1,triple_counts.2.1,triple_counts.2.2] at hb
  exact hb
#print axioms distinct
#print axioms induced
#print axioms window_directions
#print axioms triple_counts
#print axioms attains
#print axioms sharp_constant
end Snake9.TripleReturn
'''
(HERE/'lean/TripleWitness.lean').write_text(s,encoding='utf-8')
