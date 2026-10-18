import E112199Data
import DfsBankData
import CubeLocal
import E112075Complete
namespace Snake9.Regrowth.Bank112
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem prefix_match199 : ∀ i : Fin 112, E112199.pre[i.val]! = (Dfs.oriented 199)[i.val]! := by decide
theorem translate_region199 : ∀ v : Vertex, v ∈ E112199.region → vxor (192 : Vertex) v ∈ E112075.region := by decide
theorem translate_head199 : vxor (192 : Vertex) E112199.head = E112075.head := by decide
theorem entry199 (p : Snake 192) (hp : Dfs.StartsWith p (Dfs.oriented 199) 112) : False := by
  have hp' : Dfs.StartsWith p E112199.pre 112 := by
    intro i hi hpLen
    rw [prefix_match199 ⟨i,hi⟩]
    exact hp i hi hpLen
  let q := translate (suffix p) (192 : Vertex)
  apply E112075.region_exclusion q
  constructor
  · change vxor (192 : Vertex) ((suffix p).vertex 0) = E112075.head
    rw [E112199.suffix_head p hp',translate_head199]
  · intro v hv
    obtain ⟨i,rfl⟩ := hv
    exact translate_region199 _ (E112199.suffix_covered p hp' _ ⟨i,rfl⟩)
#print axioms entry199
end Snake9.Regrowth.Bank112
