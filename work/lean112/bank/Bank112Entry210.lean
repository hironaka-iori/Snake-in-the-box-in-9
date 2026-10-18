import E112210Data
import DfsBankData
import CubeLocal
import E112190Complete
namespace Snake9.Regrowth.Bank112
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem prefix_match210 : ∀ i : Fin 112, E112210.pre[i.val]! = (Dfs.oriented 210)[i.val]! := by decide
theorem translate_region210 : ∀ v : Vertex, v ∈ E112210.region → vxor (320 : Vertex) v ∈ E112190.region := by decide
theorem translate_head210 : vxor (320 : Vertex) E112210.head = E112190.head := by decide
theorem entry210 (p : Snake 192) (hp : Dfs.StartsWith p (Dfs.oriented 210) 112) : False := by
  have hp' : Dfs.StartsWith p E112210.pre 112 := by
    intro i hi hpLen
    rw [prefix_match210 ⟨i,hi⟩]
    exact hp i hi hpLen
  let q := translate (suffix p) (320 : Vertex)
  apply E112190.region_exclusion q
  constructor
  · change vxor (320 : Vertex) ((suffix p).vertex 0) = E112190.head
    rw [E112210.suffix_head p hp',translate_head210]
  · intro v hv
    obtain ⟨i,rfl⟩ := hv
    exact translate_region210 _ (E112210.suffix_covered p hp' _ ⟨i,rfl⟩)
#print axioms entry210
end Snake9.Regrowth.Bank112
