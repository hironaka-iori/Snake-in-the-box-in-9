import E112071Data
import DfsBankData
import CubeLocal
import E112190Complete
namespace Snake9.Regrowth.Bank112
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem prefix_match71 : ∀ i : Fin 112, E112071.pre[i.val]! = (Dfs.oriented 71)[i.val]! := by decide
theorem translate_region71 : ∀ v : Vertex, v ∈ E112071.region → vxor (280 : Vertex) v ∈ E112190.region := by decide
theorem translate_head71 : vxor (280 : Vertex) E112071.head = E112190.head := by decide
theorem entry71 (p : Snake 192) (hp : Dfs.StartsWith p (Dfs.oriented 71) 112) : False := by
  have hp' : Dfs.StartsWith p E112071.pre 112 := by
    intro i hi hpLen
    rw [prefix_match71 ⟨i,hi⟩]
    exact hp i hi hpLen
  let q := translate (suffix p) (280 : Vertex)
  apply E112190.region_exclusion q
  constructor
  · change vxor (280 : Vertex) ((suffix p).vertex 0) = E112190.head
    rw [E112071.suffix_head p hp',translate_head71]
  · intro v hv
    obtain ⟨i,rfl⟩ := hv
    exact translate_region71 _ (E112071.suffix_covered p hp' _ ⟨i,rfl⟩)
#print axioms entry71
end Snake9.Regrowth.Bank112
