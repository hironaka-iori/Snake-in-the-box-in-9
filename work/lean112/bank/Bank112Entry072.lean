import E112072Data
import DfsBankData
import CubeLocal
import E112187Complete
namespace Snake9.Regrowth.Bank112
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem prefix_match72 : ∀ i : Fin 112, E112072.pre[i.val]! = (Dfs.oriented 72)[i.val]! := by decide
theorem translate_region72 : ∀ v : Vertex, v ∈ E112072.region → vxor (280 : Vertex) v ∈ E112187.region := by decide
theorem translate_head72 : vxor (280 : Vertex) E112072.head = E112187.head := by decide
theorem entry72 (p : Snake 192) (hp : Dfs.StartsWith p (Dfs.oriented 72) 112) : False := by
  have hp' : Dfs.StartsWith p E112072.pre 112 := by
    intro i hi hpLen
    rw [prefix_match72 ⟨i,hi⟩]
    exact hp i hi hpLen
  let q := translate (suffix p) (280 : Vertex)
  apply E112187.region_exclusion q
  constructor
  · change vxor (280 : Vertex) ((suffix p).vertex 0) = E112187.head
    rw [E112072.suffix_head p hp',translate_head72]
  · intro v hv
    obtain ⟨i,rfl⟩ := hv
    exact translate_region72 _ (E112072.suffix_covered p hp' _ ⟨i,rfl⟩)
#print axioms entry72
end Snake9.Regrowth.Bank112
