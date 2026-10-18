import E112005Data
import DfsBankData
import CubeLocal
import E112020Complete
namespace Snake9.Regrowth.Bank112
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem prefix_match5 : ∀ i : Fin 112, E112005.pre[i.val]! = (Dfs.oriented 5)[i.val]! := by decide
theorem translate_region5 : ∀ v : Vertex, v ∈ E112005.region → vxor (361 : Vertex) v ∈ E112020.region := by decide
theorem translate_head5 : vxor (361 : Vertex) E112005.head = E112020.head := by decide
theorem entry5 (p : Snake 192) (hp : Dfs.StartsWith p (Dfs.oriented 5) 112) : False := by
  have hp' : Dfs.StartsWith p E112005.pre 112 := by
    intro i hi hpLen
    rw [prefix_match5 ⟨i,hi⟩]
    exact hp i hi hpLen
  let q := translate (suffix p) (361 : Vertex)
  apply E112020.region_exclusion q
  constructor
  · change vxor (361 : Vertex) ((suffix p).vertex 0) = E112020.head
    rw [E112005.suffix_head p hp',translate_head5]
  · intro v hv
    obtain ⟨i,rfl⟩ := hv
    exact translate_region5 _ (E112005.suffix_covered p hp' _ ⟨i,rfl⟩)
#print axioms entry5
end Snake9.Regrowth.Bank112
