import E112173Data
import DfsBankData
import CubeLocal
import E112094Complete
namespace Snake9.Regrowth.Bank112
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem prefix_match173 : ∀ i : Fin 112, E112173.pre[i.val]! = (Dfs.oriented 173)[i.val]! := by decide
theorem translate_region173 : ∀ v : Vertex, v ∈ E112173.region → vxor (22 : Vertex) v ∈ E112094.region := by decide
theorem translate_head173 : vxor (22 : Vertex) E112173.head = E112094.head := by decide
theorem entry173 (p : Snake 192) (hp : Dfs.StartsWith p (Dfs.oriented 173) 112) : False := by
  have hp' : Dfs.StartsWith p E112173.pre 112 := by
    intro i hi hpLen
    rw [prefix_match173 ⟨i,hi⟩]
    exact hp i hi hpLen
  let q := translate (suffix p) (22 : Vertex)
  apply E112094.region_exclusion q
  constructor
  · change vxor (22 : Vertex) ((suffix p).vertex 0) = E112094.head
    rw [E112173.suffix_head p hp',translate_head173]
  · intro v hv
    obtain ⟨i,rfl⟩ := hv
    exact translate_region173 _ (E112173.suffix_covered p hp' _ ⟨i,rfl⟩)
#print axioms entry173
end Snake9.Regrowth.Bank112
