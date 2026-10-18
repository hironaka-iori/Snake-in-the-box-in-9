import E112139Data
import DfsBankData
import CubeLocal
import E112123Complete
namespace Snake9.Regrowth.Bank112
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem prefix_match139 : ∀ i : Fin 112, E112139.pre[i.val]! = (Dfs.oriented 139)[i.val]! := by decide
theorem translate_region139 : ∀ v : Vertex, v ∈ E112139.region → vxor (0 : Vertex) v ∈ E112123.region := by decide
theorem translate_head139 : vxor (0 : Vertex) E112139.head = E112123.head := by decide
theorem entry139 (p : Snake 192) (hp : Dfs.StartsWith p (Dfs.oriented 139) 112) : False := by
  have hp' : Dfs.StartsWith p E112139.pre 112 := by
    intro i hi hpLen
    rw [prefix_match139 ⟨i,hi⟩]
    exact hp i hi hpLen
  let q := translate (suffix p) (0 : Vertex)
  apply E112123.region_exclusion q
  constructor
  · change vxor (0 : Vertex) ((suffix p).vertex 0) = E112123.head
    rw [E112139.suffix_head p hp',translate_head139]
  · intro v hv
    obtain ⟨i,rfl⟩ := hv
    exact translate_region139 _ (E112139.suffix_covered p hp' _ ⟨i,rfl⟩)
#print axioms entry139
end Snake9.Regrowth.Bank112
