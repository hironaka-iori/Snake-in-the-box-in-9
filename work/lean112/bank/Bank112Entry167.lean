import E112167Data
import DfsBankData
import CubeLocal
import E112094Complete
namespace Snake9.Regrowth.Bank112
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem prefix_match167 : ∀ i : Fin 112, E112167.pre[i.val]! = (Dfs.oriented 167)[i.val]! := by decide
theorem translate_region167 : ∀ v : Vertex, v ∈ E112167.region → vxor (26 : Vertex) v ∈ E112094.region := by decide
theorem translate_head167 : vxor (26 : Vertex) E112167.head = E112094.head := by decide
theorem entry167 (p : Snake 192) (hp : Dfs.StartsWith p (Dfs.oriented 167) 112) : False := by
  have hp' : Dfs.StartsWith p E112167.pre 112 := by
    intro i hi hpLen
    rw [prefix_match167 ⟨i,hi⟩]
    exact hp i hi hpLen
  let q := translate (suffix p) (26 : Vertex)
  apply E112094.region_exclusion q
  constructor
  · change vxor (26 : Vertex) ((suffix p).vertex 0) = E112094.head
    rw [E112167.suffix_head p hp',translate_head167]
  · intro v hv
    obtain ⟨i,rfl⟩ := hv
    exact translate_region167 _ (E112167.suffix_covered p hp' _ ⟨i,rfl⟩)
#print axioms entry167
end Snake9.Regrowth.Bank112
