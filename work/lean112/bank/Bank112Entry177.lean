import E112177Data
import DfsBankData
import CubeLocal
import E112175Complete
namespace Snake9.Regrowth.Bank112
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem prefix_match177 : ∀ i : Fin 112, E112177.pre[i.val]! = (Dfs.oriented 177)[i.val]! := by decide
theorem translate_region177 : ∀ v : Vertex, v ∈ E112177.region → vxor (0 : Vertex) v ∈ E112175.region := by decide
theorem translate_head177 : vxor (0 : Vertex) E112177.head = E112175.head := by decide
theorem entry177 (p : Snake 192) (hp : Dfs.StartsWith p (Dfs.oriented 177) 112) : False := by
  have hp' : Dfs.StartsWith p E112177.pre 112 := by
    intro i hi hpLen
    rw [prefix_match177 ⟨i,hi⟩]
    exact hp i hi hpLen
  let q := translate (suffix p) (0 : Vertex)
  apply E112175.region_exclusion q
  constructor
  · change vxor (0 : Vertex) ((suffix p).vertex 0) = E112175.head
    rw [E112177.suffix_head p hp',translate_head177]
  · intro v hv
    obtain ⟨i,rfl⟩ := hv
    exact translate_region177 _ (E112177.suffix_covered p hp' _ ⟨i,rfl⟩)
#print axioms entry177
end Snake9.Regrowth.Bank112
