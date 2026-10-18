import E112101Data
import DfsBankData
import CubeLocal
import E112097Complete
namespace Snake9.Regrowth.Bank112
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem prefix_match101 : ∀ i : Fin 112, E112101.pre[i.val]! = (Dfs.oriented 101)[i.val]! := by decide
theorem translate_region101 : ∀ v : Vertex, v ∈ E112101.region → vxor (0 : Vertex) v ∈ E112097.region := by decide
theorem translate_head101 : vxor (0 : Vertex) E112101.head = E112097.head := by decide
theorem entry101 (p : Snake 192) (hp : Dfs.StartsWith p (Dfs.oriented 101) 112) : False := by
  have hp' : Dfs.StartsWith p E112101.pre 112 := by
    intro i hi hpLen
    rw [prefix_match101 ⟨i,hi⟩]
    exact hp i hi hpLen
  let q := translate (suffix p) (0 : Vertex)
  apply E112097.region_exclusion q
  constructor
  · change vxor (0 : Vertex) ((suffix p).vertex 0) = E112097.head
    rw [E112101.suffix_head p hp',translate_head101]
  · intro v hv
    obtain ⟨i,rfl⟩ := hv
    exact translate_region101 _ (E112101.suffix_covered p hp' _ ⟨i,rfl⟩)
#print axioms entry101
end Snake9.Regrowth.Bank112
