import E112202Data
import DfsBankData
import CubeLocal
import E112190Complete
namespace Snake9.Regrowth.Bank112
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem prefix_match202 : ∀ i : Fin 112, E112202.pre[i.val]! = (Dfs.oriented 202)[i.val]! := by decide
theorem translate_region202 : ∀ v : Vertex, v ∈ E112202.region → vxor (320 : Vertex) v ∈ E112190.region := by decide
theorem translate_head202 : vxor (320 : Vertex) E112202.head = E112190.head := by decide
theorem entry202 (p : Snake 192) (hp : Dfs.StartsWith p (Dfs.oriented 202) 112) : False := by
  have hp' : Dfs.StartsWith p E112202.pre 112 := by
    intro i hi hpLen
    rw [prefix_match202 ⟨i,hi⟩]
    exact hp i hi hpLen
  let q := translate (suffix p) (320 : Vertex)
  apply E112190.region_exclusion q
  constructor
  · change vxor (320 : Vertex) ((suffix p).vertex 0) = E112190.head
    rw [E112202.suffix_head p hp',translate_head202]
  · intro v hv
    obtain ⟨i,rfl⟩ := hv
    exact translate_region202 _ (E112202.suffix_covered p hp' _ ⟨i,rfl⟩)
#print axioms entry202
end Snake9.Regrowth.Bank112
