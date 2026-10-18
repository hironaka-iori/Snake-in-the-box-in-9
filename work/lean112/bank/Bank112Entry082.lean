import E112082Data
import DfsBankData
import CubeLocal
import E112078Complete
namespace Snake9.Regrowth.Bank112
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem prefix_match82 : ∀ i : Fin 112, E112082.pre[i.val]! = (Dfs.oriented 82)[i.val]! := by decide
theorem translate_region82 : ∀ v : Vertex, v ∈ E112082.region → vxor (0 : Vertex) v ∈ E112078.region := by decide
theorem translate_head82 : vxor (0 : Vertex) E112082.head = E112078.head := by decide
theorem entry82 (p : Snake 192) (hp : Dfs.StartsWith p (Dfs.oriented 82) 112) : False := by
  have hp' : Dfs.StartsWith p E112082.pre 112 := by
    intro i hi hpLen
    rw [prefix_match82 ⟨i,hi⟩]
    exact hp i hi hpLen
  let q := translate (suffix p) (0 : Vertex)
  apply E112078.region_exclusion q
  constructor
  · change vxor (0 : Vertex) ((suffix p).vertex 0) = E112078.head
    rw [E112082.suffix_head p hp',translate_head82]
  · intro v hv
    obtain ⟨i,rfl⟩ := hv
    exact translate_region82 _ (E112082.suffix_covered p hp' _ ⟨i,rfl⟩)
#print axioms entry82
end Snake9.Regrowth.Bank112
