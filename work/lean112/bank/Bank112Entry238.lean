import E112238Data
import DfsBankData
import CubeLocal
import E112234Complete
namespace Snake9.Regrowth.Bank112
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem prefix_match238 : ∀ i : Fin 112, E112238.pre[i.val]! = (Dfs.oriented 238)[i.val]! := by decide
theorem translate_region238 : ∀ v : Vertex, v ∈ E112238.region → vxor (0 : Vertex) v ∈ E112234.region := by decide
theorem translate_head238 : vxor (0 : Vertex) E112238.head = E112234.head := by decide
theorem entry238 (p : Snake 192) (hp : Dfs.StartsWith p (Dfs.oriented 238) 112) : False := by
  have hp' : Dfs.StartsWith p E112238.pre 112 := by
    intro i hi hpLen
    rw [prefix_match238 ⟨i,hi⟩]
    exact hp i hi hpLen
  let q := translate (suffix p) (0 : Vertex)
  apply E112234.region_exclusion q
  constructor
  · change vxor (0 : Vertex) ((suffix p).vertex 0) = E112234.head
    rw [E112238.suffix_head p hp',translate_head238]
  · intro v hv
    obtain ⟨i,rfl⟩ := hv
    exact translate_region238 _ (E112238.suffix_covered p hp' _ ⟨i,rfl⟩)
#print axioms entry238
end Snake9.Regrowth.Bank112
