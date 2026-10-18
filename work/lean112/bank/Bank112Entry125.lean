import E112125Data
import DfsBankData
import CubeLocal
import E112121Complete
namespace Snake9.Regrowth.Bank112
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem prefix_match125 : ∀ i : Fin 112, E112125.pre[i.val]! = (Dfs.oriented 125)[i.val]! := by decide
theorem translate_region125 : ∀ v : Vertex, v ∈ E112125.region → vxor (0 : Vertex) v ∈ E112121.region := by decide
theorem translate_head125 : vxor (0 : Vertex) E112125.head = E112121.head := by decide
theorem entry125 (p : Snake 192) (hp : Dfs.StartsWith p (Dfs.oriented 125) 112) : False := by
  have hp' : Dfs.StartsWith p E112125.pre 112 := by
    intro i hi hpLen
    rw [prefix_match125 ⟨i,hi⟩]
    exact hp i hi hpLen
  let q := translate (suffix p) (0 : Vertex)
  apply E112121.region_exclusion q
  constructor
  · change vxor (0 : Vertex) ((suffix p).vertex 0) = E112121.head
    rw [E112125.suffix_head p hp',translate_head125]
  · intro v hv
    obtain ⟨i,rfl⟩ := hv
    exact translate_region125 _ (E112125.suffix_covered p hp' _ ⟨i,rfl⟩)
#print axioms entry125
end Snake9.Regrowth.Bank112
