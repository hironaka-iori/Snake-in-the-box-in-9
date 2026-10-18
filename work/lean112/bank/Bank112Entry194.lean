import E112194Data
import DfsBankData
import CubeLocal
import E112190Complete
namespace Snake9.Regrowth.Bank112
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem prefix_match194 : ∀ i : Fin 112, E112194.pre[i.val]! = (Dfs.oriented 194)[i.val]! := by decide
theorem translate_region194 : ∀ v : Vertex, v ∈ E112194.region → vxor (0 : Vertex) v ∈ E112190.region := by decide
theorem translate_head194 : vxor (0 : Vertex) E112194.head = E112190.head := by decide
theorem entry194 (p : Snake 192) (hp : Dfs.StartsWith p (Dfs.oriented 194) 112) : False := by
  have hp' : Dfs.StartsWith p E112194.pre 112 := by
    intro i hi hpLen
    rw [prefix_match194 ⟨i,hi⟩]
    exact hp i hi hpLen
  let q := translate (suffix p) (0 : Vertex)
  apply E112190.region_exclusion q
  constructor
  · change vxor (0 : Vertex) ((suffix p).vertex 0) = E112190.head
    rw [E112194.suffix_head p hp',translate_head194]
  · intro v hv
    obtain ⟨i,rfl⟩ := hv
    exact translate_region194 _ (E112194.suffix_covered p hp' _ ⟨i,rfl⟩)
#print axioms entry194
end Snake9.Regrowth.Bank112
