import E112156Data
import DfsBankData
import CubeLocal
import E112154Complete
namespace Snake9.Regrowth.Bank112
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem prefix_match156 : ∀ i : Fin 112, E112156.pre[i.val]! = (Dfs.oriented 156)[i.val]! := by decide
theorem translate_region156 : ∀ v : Vertex, v ∈ E112156.region → vxor (0 : Vertex) v ∈ E112154.region := by decide
theorem translate_head156 : vxor (0 : Vertex) E112156.head = E112154.head := by decide
theorem entry156 (p : Snake 192) (hp : Dfs.StartsWith p (Dfs.oriented 156) 112) : False := by
  have hp' : Dfs.StartsWith p E112156.pre 112 := by
    intro i hi hpLen
    rw [prefix_match156 ⟨i,hi⟩]
    exact hp i hi hpLen
  let q := translate (suffix p) (0 : Vertex)
  apply E112154.region_exclusion q
  constructor
  · change vxor (0 : Vertex) ((suffix p).vertex 0) = E112154.head
    rw [E112156.suffix_head p hp',translate_head156]
  · intro v hv
    obtain ⟨i,rfl⟩ := hv
    exact translate_region156 _ (E112156.suffix_covered p hp' _ ⟨i,rfl⟩)
#print axioms entry156
end Snake9.Regrowth.Bank112
