import E112216Data
import DfsBankData
import CubeLocal
import E112075Complete
namespace Snake9.Regrowth.Bank112
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem prefix_match216 : ∀ i : Fin 112, E112216.pre[i.val]! = (Dfs.oriented 216)[i.val]! := by decide
theorem translate_region216 : ∀ v : Vertex, v ∈ E112216.region → vxor (327 : Vertex) v ∈ E112075.region := by decide
theorem translate_head216 : vxor (327 : Vertex) E112216.head = E112075.head := by decide
theorem entry216 (p : Snake 192) (hp : Dfs.StartsWith p (Dfs.oriented 216) 112) : False := by
  have hp' : Dfs.StartsWith p E112216.pre 112 := by
    intro i hi hpLen
    rw [prefix_match216 ⟨i,hi⟩]
    exact hp i hi hpLen
  let q := translate (suffix p) (327 : Vertex)
  apply E112075.region_exclusion q
  constructor
  · change vxor (327 : Vertex) ((suffix p).vertex 0) = E112075.head
    rw [E112216.suffix_head p hp',translate_head216]
  · intro v hv
    obtain ⟨i,rfl⟩ := hv
    exact translate_region216 _ (E112216.suffix_covered p hp' _ ⟨i,rfl⟩)
#print axioms entry216
end Snake9.Regrowth.Bank112
