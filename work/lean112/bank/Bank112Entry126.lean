import E112126Data
import DfsBankData
import CubeLocal
import E112118Complete
namespace Snake9.Regrowth.Bank112
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem prefix_match126 : ∀ i : Fin 112, E112126.pre[i.val]! = (Dfs.oriented 126)[i.val]! := by decide
theorem translate_region126 : ∀ v : Vertex, v ∈ E112126.region → vxor (0 : Vertex) v ∈ E112118.region := by decide
theorem translate_head126 : vxor (0 : Vertex) E112126.head = E112118.head := by decide
theorem entry126 (p : Snake 192) (hp : Dfs.StartsWith p (Dfs.oriented 126) 112) : False := by
  have hp' : Dfs.StartsWith p E112126.pre 112 := by
    intro i hi hpLen
    rw [prefix_match126 ⟨i,hi⟩]
    exact hp i hi hpLen
  let q := translate (suffix p) (0 : Vertex)
  apply E112118.region_exclusion q
  constructor
  · change vxor (0 : Vertex) ((suffix p).vertex 0) = E112118.head
    rw [E112126.suffix_head p hp',translate_head126]
  · intro v hv
    obtain ⟨i,rfl⟩ := hv
    exact translate_region126 _ (E112126.suffix_covered p hp' _ ⟨i,rfl⟩)
#print axioms entry126
end Snake9.Regrowth.Bank112
