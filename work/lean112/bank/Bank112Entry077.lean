import E112077Data
import DfsBankData
import CubeLocal
import E112064Complete
namespace Snake9.Regrowth.Bank112
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem prefix_match77 : ∀ i : Fin 112, E112077.pre[i.val]! = (Dfs.oriented 77)[i.val]! := by decide
theorem translate_region77 : ∀ v : Vertex, v ∈ E112077.region → vxor (88 : Vertex) v ∈ E112064.region := by decide
theorem translate_head77 : vxor (88 : Vertex) E112077.head = E112064.head := by decide
theorem entry77 (p : Snake 192) (hp : Dfs.StartsWith p (Dfs.oriented 77) 112) : False := by
  have hp' : Dfs.StartsWith p E112077.pre 112 := by
    intro i hi hpLen
    rw [prefix_match77 ⟨i,hi⟩]
    exact hp i hi hpLen
  let q := translate (suffix p) (88 : Vertex)
  apply E112064.region_exclusion q
  constructor
  · change vxor (88 : Vertex) ((suffix p).vertex 0) = E112064.head
    rw [E112077.suffix_head p hp',translate_head77]
  · intro v hv
    obtain ⟨i,rfl⟩ := hv
    exact translate_region77 _ (E112077.suffix_covered p hp' _ ⟨i,rfl⟩)
#print axioms entry77
end Snake9.Regrowth.Bank112
