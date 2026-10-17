import E112219Data
import DfsBankData
import CubeLocal
import E112225Complete
namespace Snake9.Regrowth.Bank112
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem prefix_match219 : ∀ i : Fin 112, E112219.pre[i.val]! = (Dfs.oriented 219)[i.val]! := by decide
theorem translate_region219 : ∀ v : Vertex, v ∈ E112219.region → vxor (78 : Vertex) v ∈ E112225.region := by decide
theorem translate_head219 : vxor (78 : Vertex) E112219.head = E112225.head := by decide
theorem entry219 (p : Snake 192) (hp : Dfs.StartsWith p (Dfs.oriented 219) 112) : False := by
  have hp' : Dfs.StartsWith p E112219.pre 112 := by
    intro i hi hpLen
    rw [prefix_match219 ⟨i,hi⟩]
    exact hp i hi hpLen
  let q := translate (suffix p) (78 : Vertex)
  apply E112225.region_exclusion q
  constructor
  · change vxor (78 : Vertex) ((suffix p).vertex 0) = E112225.head
    rw [E112219.suffix_head p hp',translate_head219]
  · intro v hv
    obtain ⟨i,rfl⟩ := hv
    exact translate_region219 _ (E112219.suffix_covered p hp' _ ⟨i,rfl⟩)
#print axioms entry219
end Snake9.Regrowth.Bank112
