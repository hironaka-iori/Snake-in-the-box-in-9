import E112229Data
import DfsBankData
import CubeLocal
import E112225Complete
namespace Snake9.Regrowth.Bank112
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem prefix_match229 : ∀ i : Fin 112, E112229.pre[i.val]! = (Dfs.oriented 229)[i.val]! := by decide
theorem translate_region229 : ∀ v : Vertex, v ∈ E112229.region → vxor (12 : Vertex) v ∈ E112225.region := by decide
theorem translate_head229 : vxor (12 : Vertex) E112229.head = E112225.head := by decide
theorem entry229 (p : Snake 192) (hp : Dfs.StartsWith p (Dfs.oriented 229) 112) : False := by
  have hp' : Dfs.StartsWith p E112229.pre 112 := by
    intro i hi hpLen
    rw [prefix_match229 ⟨i,hi⟩]
    exact hp i hi hpLen
  let q := translate (suffix p) (12 : Vertex)
  apply E112225.region_exclusion q
  constructor
  · change vxor (12 : Vertex) ((suffix p).vertex 0) = E112225.head
    rw [E112229.suffix_head p hp',translate_head229]
  · intro v hv
    obtain ⟨i,rfl⟩ := hv
    exact translate_region229 _ (E112229.suffix_covered p hp' _ ⟨i,rfl⟩)
#print axioms entry229
end Snake9.Regrowth.Bank112
