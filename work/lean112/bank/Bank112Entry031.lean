import E112031Data
import DfsBankData
import CubeLocal
import E112027Complete
namespace Snake9.Regrowth.Bank112
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem prefix_match31 : ∀ i : Fin 112, E112031.pre[i.val]! = (Dfs.oriented 31)[i.val]! := by decide
theorem translate_region31 : ∀ v : Vertex, v ∈ E112031.region → vxor (0 : Vertex) v ∈ E112027.region := by decide
theorem translate_head31 : vxor (0 : Vertex) E112031.head = E112027.head := by decide
theorem entry31 (p : Snake 192) (hp : Dfs.StartsWith p (Dfs.oriented 31) 112) : False := by
  have hp' : Dfs.StartsWith p E112031.pre 112 := by
    intro i hi hpLen
    rw [prefix_match31 ⟨i,hi⟩]
    exact hp i hi hpLen
  let q := translate (suffix p) (0 : Vertex)
  apply E112027.region_exclusion q
  constructor
  · change vxor (0 : Vertex) ((suffix p).vertex 0) = E112027.head
    rw [E112031.suffix_head p hp',translate_head31]
  · intro v hv
    obtain ⟨i,rfl⟩ := hv
    exact translate_region31 _ (E112031.suffix_covered p hp' _ ⟨i,rfl⟩)
#print axioms entry31
end Snake9.Regrowth.Bank112
