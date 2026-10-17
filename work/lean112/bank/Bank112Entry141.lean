import E112141Data
import DfsBankData
import CubeLocal
import E112123Complete
namespace Snake9.Regrowth.Bank112
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem prefix_match141 : ∀ i : Fin 112, E112141.pre[i.val]! = (Dfs.oriented 141)[i.val]! := by decide
theorem translate_region141 : ∀ v : Vertex, v ∈ E112141.region → vxor (0 : Vertex) v ∈ E112123.region := by decide
theorem translate_head141 : vxor (0 : Vertex) E112141.head = E112123.head := by decide
theorem entry141 (p : Snake 192) (hp : Dfs.StartsWith p (Dfs.oriented 141) 112) : False := by
  have hp' : Dfs.StartsWith p E112141.pre 112 := by
    intro i hi hpLen
    rw [prefix_match141 ⟨i,hi⟩]
    exact hp i hi hpLen
  let q := translate (suffix p) (0 : Vertex)
  apply E112123.region_exclusion q
  constructor
  · change vxor (0 : Vertex) ((suffix p).vertex 0) = E112123.head
    rw [E112141.suffix_head p hp',translate_head141]
  · intro v hv
    obtain ⟨i,rfl⟩ := hv
    exact translate_region141 _ (E112141.suffix_covered p hp' _ ⟨i,rfl⟩)
#print axioms entry141
end Snake9.Regrowth.Bank112
