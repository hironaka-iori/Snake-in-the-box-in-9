import E112220Data
import DfsBankData
import CubeLocal
import E112098Complete
namespace Snake9.Regrowth.Bank112
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem prefix_match220 : ∀ i : Fin 112, E112220.pre[i.val]! = (Dfs.oriented 220)[i.val]! := by decide
theorem translate_region220 : ∀ v : Vertex, v ∈ E112220.region → vxor (113 : Vertex) v ∈ E112098.region := by decide
theorem translate_head220 : vxor (113 : Vertex) E112220.head = E112098.head := by decide
theorem entry220 (p : Snake 192) (hp : Dfs.StartsWith p (Dfs.oriented 220) 112) : False := by
  have hp' : Dfs.StartsWith p E112220.pre 112 := by
    intro i hi hpLen
    rw [prefix_match220 ⟨i,hi⟩]
    exact hp i hi hpLen
  let q := translate (suffix p) (113 : Vertex)
  apply E112098.region_exclusion q
  constructor
  · change vxor (113 : Vertex) ((suffix p).vertex 0) = E112098.head
    rw [E112220.suffix_head p hp',translate_head220]
  · intro v hv
    obtain ⟨i,rfl⟩ := hv
    exact translate_region220 _ (E112220.suffix_covered p hp' _ ⟨i,rfl⟩)
#print axioms entry220
end Snake9.Regrowth.Bank112
