import E112117Data
import DfsBankData
import CubeLocal
import E112115Complete
namespace Snake9.Regrowth.Bank112
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem prefix_match117 : ∀ i : Fin 112, E112117.pre[i.val]! = (Dfs.oriented 117)[i.val]! := by decide
theorem translate_region117 : ∀ v : Vertex, v ∈ E112117.region → vxor (17 : Vertex) v ∈ E112115.region := by decide
theorem translate_head117 : vxor (17 : Vertex) E112117.head = E112115.head := by decide
theorem entry117 (p : Snake 192) (hp : Dfs.StartsWith p (Dfs.oriented 117) 112) : False := by
  have hp' : Dfs.StartsWith p E112117.pre 112 := by
    intro i hi hpLen
    rw [prefix_match117 ⟨i,hi⟩]
    exact hp i hi hpLen
  let q := translate (suffix p) (17 : Vertex)
  apply E112115.region_exclusion q
  constructor
  · change vxor (17 : Vertex) ((suffix p).vertex 0) = E112115.head
    rw [E112117.suffix_head p hp',translate_head117]
  · intro v hv
    obtain ⟨i,rfl⟩ := hv
    exact translate_region117 _ (E112117.suffix_covered p hp' _ ⟨i,rfl⟩)
#print axioms entry117
end Snake9.Regrowth.Bank112
