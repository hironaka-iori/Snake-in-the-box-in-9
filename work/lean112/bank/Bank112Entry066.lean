import E112066Data
import DfsBankData
import CubeLocal
import E112064Complete
namespace Snake9.Regrowth.Bank112
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem prefix_match66 : ∀ i : Fin 112, E112066.pre[i.val]! = (Dfs.oriented 66)[i.val]! := by decide
theorem translate_region66 : ∀ v : Vertex, v ∈ E112066.region → vxor (0 : Vertex) v ∈ E112064.region := by decide
theorem translate_head66 : vxor (0 : Vertex) E112066.head = E112064.head := by decide
theorem entry66 (p : Snake 192) (hp : Dfs.StartsWith p (Dfs.oriented 66) 112) : False := by
  have hp' : Dfs.StartsWith p E112066.pre 112 := by
    intro i hi hpLen
    rw [prefix_match66 ⟨i,hi⟩]
    exact hp i hi hpLen
  let q := translate (suffix p) (0 : Vertex)
  apply E112064.region_exclusion q
  constructor
  · change vxor (0 : Vertex) ((suffix p).vertex 0) = E112064.head
    rw [E112066.suffix_head p hp',translate_head66]
  · intro v hv
    obtain ⟨i,rfl⟩ := hv
    exact translate_region66 _ (E112066.suffix_covered p hp' _ ⟨i,rfl⟩)
#print axioms entry66
end Snake9.Regrowth.Bank112
