import E112135Data
import DfsBankData
import CubeLocal
import E112123Complete
namespace Snake9.Regrowth.Bank112
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem prefix_match135 : ∀ i : Fin 112, E112135.pre[i.val]! = (Dfs.oriented 135)[i.val]! := by decide
theorem translate_region135 : ∀ v : Vertex, v ∈ E112135.region → vxor (0 : Vertex) v ∈ E112123.region := by decide
theorem translate_head135 : vxor (0 : Vertex) E112135.head = E112123.head := by decide
theorem entry135 (p : Snake 192) (hp : Dfs.StartsWith p (Dfs.oriented 135) 112) : False := by
  have hp' : Dfs.StartsWith p E112135.pre 112 := by
    intro i hi hpLen
    rw [prefix_match135 ⟨i,hi⟩]
    exact hp i hi hpLen
  let q := translate (suffix p) (0 : Vertex)
  apply E112123.region_exclusion q
  constructor
  · change vxor (0 : Vertex) ((suffix p).vertex 0) = E112123.head
    rw [E112135.suffix_head p hp',translate_head135]
  · intro v hv
    obtain ⟨i,rfl⟩ := hv
    exact translate_region135 _ (E112135.suffix_covered p hp' _ ⟨i,rfl⟩)
#print axioms entry135
end Snake9.Regrowth.Bank112
