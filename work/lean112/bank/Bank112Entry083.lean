import E112083Data
import DfsBankData
import CubeLocal
import E112079Complete
namespace Snake9.Regrowth.Bank112
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem prefix_match83 : ∀ i : Fin 112, E112083.pre[i.val]! = (Dfs.oriented 83)[i.val]! := by decide
theorem translate_region83 : ∀ v : Vertex, v ∈ E112083.region → vxor (0 : Vertex) v ∈ E112079.region := by decide
theorem translate_head83 : vxor (0 : Vertex) E112083.head = E112079.head := by decide
theorem entry83 (p : Snake 192) (hp : Dfs.StartsWith p (Dfs.oriented 83) 112) : False := by
  have hp' : Dfs.StartsWith p E112083.pre 112 := by
    intro i hi hpLen
    rw [prefix_match83 ⟨i,hi⟩]
    exact hp i hi hpLen
  let q := translate (suffix p) (0 : Vertex)
  apply E112079.region_exclusion q
  constructor
  · change vxor (0 : Vertex) ((suffix p).vertex 0) = E112079.head
    rw [E112083.suffix_head p hp',translate_head83]
  · intro v hv
    obtain ⟨i,rfl⟩ := hv
    exact translate_region83 _ (E112083.suffix_covered p hp' _ ⟨i,rfl⟩)
#print axioms entry83
end Snake9.Regrowth.Bank112
