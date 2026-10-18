import E112142Data
import DfsBankData
import CubeLocal
import E112120Complete
namespace Snake9.Regrowth.Bank112
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem prefix_match142 : ∀ i : Fin 112, E112142.pre[i.val]! = (Dfs.oriented 142)[i.val]! := by decide
theorem translate_region142 : ∀ v : Vertex, v ∈ E112142.region → vxor (0 : Vertex) v ∈ E112120.region := by decide
theorem translate_head142 : vxor (0 : Vertex) E112142.head = E112120.head := by decide
theorem entry142 (p : Snake 192) (hp : Dfs.StartsWith p (Dfs.oriented 142) 112) : False := by
  have hp' : Dfs.StartsWith p E112142.pre 112 := by
    intro i hi hpLen
    rw [prefix_match142 ⟨i,hi⟩]
    exact hp i hi hpLen
  let q := translate (suffix p) (0 : Vertex)
  apply E112120.region_exclusion q
  constructor
  · change vxor (0 : Vertex) ((suffix p).vertex 0) = E112120.head
    rw [E112142.suffix_head p hp',translate_head142]
  · intro v hv
    obtain ⟨i,rfl⟩ := hv
    exact translate_region142 _ (E112142.suffix_covered p hp' _ ⟨i,rfl⟩)
#print axioms entry142
end Snake9.Regrowth.Bank112
