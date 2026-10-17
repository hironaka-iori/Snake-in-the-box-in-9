import E112132Data
import DfsBankData
import CubeLocal
import E112120Complete
namespace Snake9.Regrowth.Bank112
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem prefix_match132 : ∀ i : Fin 112, E112132.pre[i.val]! = (Dfs.oriented 132)[i.val]! := by decide
theorem translate_region132 : ∀ v : Vertex, v ∈ E112132.region → vxor (0 : Vertex) v ∈ E112120.region := by decide
theorem translate_head132 : vxor (0 : Vertex) E112132.head = E112120.head := by decide
theorem entry132 (p : Snake 192) (hp : Dfs.StartsWith p (Dfs.oriented 132) 112) : False := by
  have hp' : Dfs.StartsWith p E112132.pre 112 := by
    intro i hi hpLen
    rw [prefix_match132 ⟨i,hi⟩]
    exact hp i hi hpLen
  let q := translate (suffix p) (0 : Vertex)
  apply E112120.region_exclusion q
  constructor
  · change vxor (0 : Vertex) ((suffix p).vertex 0) = E112120.head
    rw [E112132.suffix_head p hp',translate_head132]
  · intro v hv
    obtain ⟨i,rfl⟩ := hv
    exact translate_region132 _ (E112132.suffix_covered p hp' _ ⟨i,rfl⟩)
#print axioms entry132
end Snake9.Regrowth.Bank112
