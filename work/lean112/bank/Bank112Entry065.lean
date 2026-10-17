import E112065Data
import DfsBankData
import CubeLocal
import E112190Complete
namespace Snake9.Regrowth.Bank112
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem prefix_match65 : ∀ i : Fin 112, E112065.pre[i.val]! = (Dfs.oriented 65)[i.val]! := by decide
theorem translate_region65 : ∀ v : Vertex, v ∈ E112065.region → vxor (280 : Vertex) v ∈ E112190.region := by decide
theorem translate_head65 : vxor (280 : Vertex) E112065.head = E112190.head := by decide
theorem entry65 (p : Snake 192) (hp : Dfs.StartsWith p (Dfs.oriented 65) 112) : False := by
  have hp' : Dfs.StartsWith p E112065.pre 112 := by
    intro i hi hpLen
    rw [prefix_match65 ⟨i,hi⟩]
    exact hp i hi hpLen
  let q := translate (suffix p) (280 : Vertex)
  apply E112190.region_exclusion q
  constructor
  · change vxor (280 : Vertex) ((suffix p).vertex 0) = E112190.head
    rw [E112065.suffix_head p hp',translate_head65]
  · intro v hv
    obtain ⟨i,rfl⟩ := hv
    exact translate_region65 _ (E112065.suffix_covered p hp' _ ⟨i,rfl⟩)
#print axioms entry65
end Snake9.Regrowth.Bank112
