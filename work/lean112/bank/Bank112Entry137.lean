import E112137Data
import DfsBankData
import CubeLocal
import E112123Complete
namespace Snake9.Regrowth.Bank112
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem prefix_match137 : ∀ i : Fin 112, E112137.pre[i.val]! = (Dfs.oriented 137)[i.val]! := by decide
theorem translate_region137 : ∀ v : Vertex, v ∈ E112137.region → vxor (0 : Vertex) v ∈ E112123.region := by decide
theorem translate_head137 : vxor (0 : Vertex) E112137.head = E112123.head := by decide
theorem entry137 (p : Snake 192) (hp : Dfs.StartsWith p (Dfs.oriented 137) 112) : False := by
  have hp' : Dfs.StartsWith p E112137.pre 112 := by
    intro i hi hpLen
    rw [prefix_match137 ⟨i,hi⟩]
    exact hp i hi hpLen
  let q := translate (suffix p) (0 : Vertex)
  apply E112123.region_exclusion q
  constructor
  · change vxor (0 : Vertex) ((suffix p).vertex 0) = E112123.head
    rw [E112137.suffix_head p hp',translate_head137]
  · intro v hv
    obtain ⟨i,rfl⟩ := hv
    exact translate_region137 _ (E112137.suffix_covered p hp' _ ⟨i,rfl⟩)
#print axioms entry137
end Snake9.Regrowth.Bank112
