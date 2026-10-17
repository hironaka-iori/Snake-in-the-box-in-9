import E112085Data
import DfsBankData
import CubeLocal
import E112064Complete
namespace Snake9.Regrowth.Bank112
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem prefix_match85 : ∀ i : Fin 112, E112085.pre[i.val]! = (Dfs.oriented 85)[i.val]! := by decide
theorem translate_region85 : ∀ v : Vertex, v ∈ E112085.region → vxor (88 : Vertex) v ∈ E112064.region := by decide
theorem translate_head85 : vxor (88 : Vertex) E112085.head = E112064.head := by decide
theorem entry85 (p : Snake 192) (hp : Dfs.StartsWith p (Dfs.oriented 85) 112) : False := by
  have hp' : Dfs.StartsWith p E112085.pre 112 := by
    intro i hi hpLen
    rw [prefix_match85 ⟨i,hi⟩]
    exact hp i hi hpLen
  let q := translate (suffix p) (88 : Vertex)
  apply E112064.region_exclusion q
  constructor
  · change vxor (88 : Vertex) ((suffix p).vertex 0) = E112064.head
    rw [E112085.suffix_head p hp',translate_head85]
  · intro v hv
    obtain ⟨i,rfl⟩ := hv
    exact translate_region85 _ (E112085.suffix_covered p hp' _ ⟨i,rfl⟩)
#print axioms entry85
end Snake9.Regrowth.Bank112
