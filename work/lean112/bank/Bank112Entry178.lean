import E112178Data
import DfsBankData
import CubeLocal
import E112174Complete
namespace Snake9.Regrowth.Bank112
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem prefix_match178 : ∀ i : Fin 112, E112178.pre[i.val]! = (Dfs.oriented 178)[i.val]! := by decide
theorem translate_region178 : ∀ v : Vertex, v ∈ E112178.region → vxor (0 : Vertex) v ∈ E112174.region := by decide
theorem translate_head178 : vxor (0 : Vertex) E112178.head = E112174.head := by decide
theorem entry178 (p : Snake 192) (hp : Dfs.StartsWith p (Dfs.oriented 178) 112) : False := by
  have hp' : Dfs.StartsWith p E112178.pre 112 := by
    intro i hi hpLen
    rw [prefix_match178 ⟨i,hi⟩]
    exact hp i hi hpLen
  let q := translate (suffix p) (0 : Vertex)
  apply E112174.region_exclusion q
  constructor
  · change vxor (0 : Vertex) ((suffix p).vertex 0) = E112174.head
    rw [E112178.suffix_head p hp',translate_head178]
  · intro v hv
    obtain ⟨i,rfl⟩ := hv
    exact translate_region178 _ (E112178.suffix_covered p hp' _ ⟨i,rfl⟩)
#print axioms entry178
end Snake9.Regrowth.Bank112
