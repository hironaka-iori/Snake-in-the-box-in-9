import E112112Data
import DfsBankData
import CubeLocal
import E112110Complete
namespace Snake9.Regrowth.Bank112
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem prefix_match112 : ∀ i : Fin 112, E112112.pre[i.val]! = (Dfs.oriented 112)[i.val]! := by decide
theorem translate_region112 : ∀ v : Vertex, v ∈ E112112.region → vxor (0 : Vertex) v ∈ E112110.region := by decide
theorem translate_head112 : vxor (0 : Vertex) E112112.head = E112110.head := by decide
theorem entry112 (p : Snake 192) (hp : Dfs.StartsWith p (Dfs.oriented 112) 112) : False := by
  have hp' : Dfs.StartsWith p E112112.pre 112 := by
    intro i hi hpLen
    rw [prefix_match112 ⟨i,hi⟩]
    exact hp i hi hpLen
  let q := translate (suffix p) (0 : Vertex)
  apply E112110.region_exclusion q
  constructor
  · change vxor (0 : Vertex) ((suffix p).vertex 0) = E112110.head
    rw [E112112.suffix_head p hp',translate_head112]
  · intro v hv
    obtain ⟨i,rfl⟩ := hv
    exact translate_region112 _ (E112112.suffix_covered p hp' _ ⟨i,rfl⟩)
#print axioms entry112
end Snake9.Regrowth.Bank112
