import E112122Data
import DfsBankData
import CubeLocal
import E112118Complete
namespace Snake9.Regrowth.Bank112
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem prefix_match122 : ∀ i : Fin 112, E112122.pre[i.val]! = (Dfs.oriented 122)[i.val]! := by decide
theorem translate_region122 : ∀ v : Vertex, v ∈ E112122.region → vxor (0 : Vertex) v ∈ E112118.region := by decide
theorem translate_head122 : vxor (0 : Vertex) E112122.head = E112118.head := by decide
theorem entry122 (p : Snake 192) (hp : Dfs.StartsWith p (Dfs.oriented 122) 112) : False := by
  have hp' : Dfs.StartsWith p E112122.pre 112 := by
    intro i hi hpLen
    rw [prefix_match122 ⟨i,hi⟩]
    exact hp i hi hpLen
  let q := translate (suffix p) (0 : Vertex)
  apply E112118.region_exclusion q
  constructor
  · change vxor (0 : Vertex) ((suffix p).vertex 0) = E112118.head
    rw [E112122.suffix_head p hp',translate_head122]
  · intro v hv
    obtain ⟨i,rfl⟩ := hv
    exact translate_region122 _ (E112122.suffix_covered p hp' _ ⟨i,rfl⟩)
#print axioms entry122
end Snake9.Regrowth.Bank112
