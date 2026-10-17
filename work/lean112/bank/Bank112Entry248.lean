import E112248Data
import DfsBankData
import CubeLocal
import E112246Complete
namespace Snake9.Regrowth.Bank112
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem prefix_match248 : ∀ i : Fin 112, E112248.pre[i.val]! = (Dfs.oriented 248)[i.val]! := by decide
theorem translate_region248 : ∀ v : Vertex, v ∈ E112248.region → vxor (0 : Vertex) v ∈ E112246.region := by decide
theorem translate_head248 : vxor (0 : Vertex) E112248.head = E112246.head := by decide
theorem entry248 (p : Snake 192) (hp : Dfs.StartsWith p (Dfs.oriented 248) 112) : False := by
  have hp' : Dfs.StartsWith p E112248.pre 112 := by
    intro i hi hpLen
    rw [prefix_match248 ⟨i,hi⟩]
    exact hp i hi hpLen
  let q := translate (suffix p) (0 : Vertex)
  apply E112246.region_exclusion q
  constructor
  · change vxor (0 : Vertex) ((suffix p).vertex 0) = E112246.head
    rw [E112248.suffix_head p hp',translate_head248]
  · intro v hv
    obtain ⟨i,rfl⟩ := hv
    exact translate_region248 _ (E112248.suffix_covered p hp' _ ⟨i,rfl⟩)
#print axioms entry248
end Snake9.Regrowth.Bank112
