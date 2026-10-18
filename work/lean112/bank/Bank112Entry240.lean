import E112240Data
import DfsBankData
import CubeLocal
import E112234Complete
namespace Snake9.Regrowth.Bank112
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem prefix_match240 : ∀ i : Fin 112, E112240.pre[i.val]! = (Dfs.oriented 240)[i.val]! := by decide
theorem translate_region240 : ∀ v : Vertex, v ∈ E112240.region → vxor (0 : Vertex) v ∈ E112234.region := by decide
theorem translate_head240 : vxor (0 : Vertex) E112240.head = E112234.head := by decide
theorem entry240 (p : Snake 192) (hp : Dfs.StartsWith p (Dfs.oriented 240) 112) : False := by
  have hp' : Dfs.StartsWith p E112240.pre 112 := by
    intro i hi hpLen
    rw [prefix_match240 ⟨i,hi⟩]
    exact hp i hi hpLen
  let q := translate (suffix p) (0 : Vertex)
  apply E112234.region_exclusion q
  constructor
  · change vxor (0 : Vertex) ((suffix p).vertex 0) = E112234.head
    rw [E112240.suffix_head p hp',translate_head240]
  · intro v hv
    obtain ⟨i,rfl⟩ := hv
    exact translate_region240 _ (E112240.suffix_covered p hp' _ ⟨i,rfl⟩)
#print axioms entry240
end Snake9.Regrowth.Bank112
