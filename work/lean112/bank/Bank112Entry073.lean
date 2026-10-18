import E112073Data
import DfsBankData
import CubeLocal
import E112186Complete
namespace Snake9.Regrowth.Bank112
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem prefix_match73 : ∀ i : Fin 112, E112073.pre[i.val]! = (Dfs.oriented 73)[i.val]! := by decide
theorem translate_region73 : ∀ v : Vertex, v ∈ E112073.region → vxor (280 : Vertex) v ∈ E112186.region := by decide
theorem translate_head73 : vxor (280 : Vertex) E112073.head = E112186.head := by decide
theorem entry73 (p : Snake 192) (hp : Dfs.StartsWith p (Dfs.oriented 73) 112) : False := by
  have hp' : Dfs.StartsWith p E112073.pre 112 := by
    intro i hi hpLen
    rw [prefix_match73 ⟨i,hi⟩]
    exact hp i hi hpLen
  let q := translate (suffix p) (280 : Vertex)
  apply E112186.region_exclusion q
  constructor
  · change vxor (280 : Vertex) ((suffix p).vertex 0) = E112186.head
    rw [E112073.suffix_head p hp',translate_head73]
  · intro v hv
    obtain ⟨i,rfl⟩ := hv
    exact translate_region73 _ (E112073.suffix_covered p hp' _ ⟨i,rfl⟩)
#print axioms entry73
end Snake9.Regrowth.Bank112
