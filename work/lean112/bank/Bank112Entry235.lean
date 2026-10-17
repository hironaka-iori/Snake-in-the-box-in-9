import E112235Data
import DfsBankData
import CubeLocal
import E112175Complete
namespace Snake9.Regrowth.Bank112
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem prefix_match235 : ∀ i : Fin 112, E112235.pre[i.val]! = (Dfs.oriented 235)[i.val]! := by decide
theorem translate_region235 : ∀ v : Vertex, v ∈ E112235.region → vxor (0 : Vertex) v ∈ E112175.region := by decide
theorem translate_head235 : vxor (0 : Vertex) E112235.head = E112175.head := by decide
theorem entry235 (p : Snake 192) (hp : Dfs.StartsWith p (Dfs.oriented 235) 112) : False := by
  have hp' : Dfs.StartsWith p E112235.pre 112 := by
    intro i hi hpLen
    rw [prefix_match235 ⟨i,hi⟩]
    exact hp i hi hpLen
  let q := translate (suffix p) (0 : Vertex)
  apply E112175.region_exclusion q
  constructor
  · change vxor (0 : Vertex) ((suffix p).vertex 0) = E112175.head
    rw [E112235.suffix_head p hp',translate_head235]
  · intro v hv
    obtain ⟨i,rfl⟩ := hv
    exact translate_region235 _ (E112235.suffix_covered p hp' _ ⟨i,rfl⟩)
#print axioms entry235
end Snake9.Regrowth.Bank112
