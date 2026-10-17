import E112140Data
import DfsBankData
import CubeLocal
import E112118Complete
namespace Snake9.Regrowth.Bank112
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem prefix_match140 : ∀ i : Fin 112, E112140.pre[i.val]! = (Dfs.oriented 140)[i.val]! := by decide
theorem translate_region140 : ∀ v : Vertex, v ∈ E112140.region → vxor (0 : Vertex) v ∈ E112118.region := by decide
theorem translate_head140 : vxor (0 : Vertex) E112140.head = E112118.head := by decide
theorem entry140 (p : Snake 192) (hp : Dfs.StartsWith p (Dfs.oriented 140) 112) : False := by
  have hp' : Dfs.StartsWith p E112140.pre 112 := by
    intro i hi hpLen
    rw [prefix_match140 ⟨i,hi⟩]
    exact hp i hi hpLen
  let q := translate (suffix p) (0 : Vertex)
  apply E112118.region_exclusion q
  constructor
  · change vxor (0 : Vertex) ((suffix p).vertex 0) = E112118.head
    rw [E112140.suffix_head p hp',translate_head140]
  · intro v hv
    obtain ⟨i,rfl⟩ := hv
    exact translate_region140 _ (E112140.suffix_covered p hp' _ ⟨i,rfl⟩)
#print axioms entry140
end Snake9.Regrowth.Bank112
