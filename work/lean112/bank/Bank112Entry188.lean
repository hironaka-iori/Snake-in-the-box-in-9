import E112188Data
import DfsBankData
import CubeLocal
import E112186Complete
namespace Snake9.Regrowth.Bank112
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem prefix_match188 : ∀ i : Fin 112, E112188.pre[i.val]! = (Dfs.oriented 188)[i.val]! := by decide
theorem translate_region188 : ∀ v : Vertex, v ∈ E112188.region → vxor (0 : Vertex) v ∈ E112186.region := by decide
theorem translate_head188 : vxor (0 : Vertex) E112188.head = E112186.head := by decide
theorem entry188 (p : Snake 192) (hp : Dfs.StartsWith p (Dfs.oriented 188) 112) : False := by
  have hp' : Dfs.StartsWith p E112188.pre 112 := by
    intro i hi hpLen
    rw [prefix_match188 ⟨i,hi⟩]
    exact hp i hi hpLen
  let q := translate (suffix p) (0 : Vertex)
  apply E112186.region_exclusion q
  constructor
  · change vxor (0 : Vertex) ((suffix p).vertex 0) = E112186.head
    rw [E112188.suffix_head p hp',translate_head188]
  · intro v hv
    obtain ⟨i,rfl⟩ := hv
    exact translate_region188 _ (E112188.suffix_covered p hp' _ ⟨i,rfl⟩)
#print axioms entry188
end Snake9.Regrowth.Bank112
