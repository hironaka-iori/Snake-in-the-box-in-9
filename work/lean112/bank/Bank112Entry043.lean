import E112043Data
import DfsBankData
import CubeLocal
import E112040Complete
namespace Snake9.Regrowth.Bank112
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem prefix_match43 : ∀ i : Fin 112, E112043.pre[i.val]! = (Dfs.oriented 43)[i.val]! := by decide
theorem translate_region43 : ∀ v : Vertex, v ∈ E112043.region → vxor (425 : Vertex) v ∈ E112040.region := by decide
theorem translate_head43 : vxor (425 : Vertex) E112043.head = E112040.head := by decide
theorem entry43 (p : Snake 192) (hp : Dfs.StartsWith p (Dfs.oriented 43) 112) : False := by
  have hp' : Dfs.StartsWith p E112043.pre 112 := by
    intro i hi hpLen
    rw [prefix_match43 ⟨i,hi⟩]
    exact hp i hi hpLen
  let q := translate (suffix p) (425 : Vertex)
  apply E112040.region_exclusion q
  constructor
  · change vxor (425 : Vertex) ((suffix p).vertex 0) = E112040.head
    rw [E112043.suffix_head p hp',translate_head43]
  · intro v hv
    obtain ⟨i,rfl⟩ := hv
    exact translate_region43 _ (E112043.suffix_covered p hp' _ ⟨i,rfl⟩)
#print axioms entry43
end Snake9.Regrowth.Bank112
