import E112028Data
import DfsBankData
import CubeLocal
import E112024Complete
namespace Snake9.Regrowth.Bank112
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem prefix_match28 : ∀ i : Fin 112, E112028.pre[i.val]! = (Dfs.oriented 28)[i.val]! := by decide
theorem translate_region28 : ∀ v : Vertex, v ∈ E112028.region → vxor (0 : Vertex) v ∈ E112024.region := by decide
theorem translate_head28 : vxor (0 : Vertex) E112028.head = E112024.head := by decide
theorem entry28 (p : Snake 192) (hp : Dfs.StartsWith p (Dfs.oriented 28) 112) : False := by
  have hp' : Dfs.StartsWith p E112028.pre 112 := by
    intro i hi hpLen
    rw [prefix_match28 ⟨i,hi⟩]
    exact hp i hi hpLen
  let q := translate (suffix p) (0 : Vertex)
  apply E112024.region_exclusion q
  constructor
  · change vxor (0 : Vertex) ((suffix p).vertex 0) = E112024.head
    rw [E112028.suffix_head p hp',translate_head28]
  · intro v hv
    obtain ⟨i,rfl⟩ := hv
    exact translate_region28 _ (E112028.suffix_covered p hp' _ ⟨i,rfl⟩)
#print axioms entry28
end Snake9.Regrowth.Bank112
