import E112143Data
import DfsBankData
import CubeLocal
import E112121Complete
namespace Snake9.Regrowth.Bank112
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem prefix_match143 : ∀ i : Fin 112, E112143.pre[i.val]! = (Dfs.oriented 143)[i.val]! := by decide
theorem translate_region143 : ∀ v : Vertex, v ∈ E112143.region → vxor (0 : Vertex) v ∈ E112121.region := by decide
theorem translate_head143 : vxor (0 : Vertex) E112143.head = E112121.head := by decide
theorem entry143 (p : Snake 192) (hp : Dfs.StartsWith p (Dfs.oriented 143) 112) : False := by
  have hp' : Dfs.StartsWith p E112143.pre 112 := by
    intro i hi hpLen
    rw [prefix_match143 ⟨i,hi⟩]
    exact hp i hi hpLen
  let q := translate (suffix p) (0 : Vertex)
  apply E112121.region_exclusion q
  constructor
  · change vxor (0 : Vertex) ((suffix p).vertex 0) = E112121.head
    rw [E112143.suffix_head p hp',translate_head143]
  · intro v hv
    obtain ⟨i,rfl⟩ := hv
    exact translate_region143 _ (E112143.suffix_covered p hp' _ ⟨i,rfl⟩)
#print axioms entry143
end Snake9.Regrowth.Bank112
