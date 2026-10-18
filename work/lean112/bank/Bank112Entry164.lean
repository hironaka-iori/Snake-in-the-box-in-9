import E112164Data
import DfsBankData
import CubeLocal
import E112154Complete
namespace Snake9.Regrowth.Bank112
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem prefix_match164 : ∀ i : Fin 112, E112164.pre[i.val]! = (Dfs.oriented 164)[i.val]! := by decide
theorem translate_region164 : ∀ v : Vertex, v ∈ E112164.region → vxor (0 : Vertex) v ∈ E112154.region := by decide
theorem translate_head164 : vxor (0 : Vertex) E112164.head = E112154.head := by decide
theorem entry164 (p : Snake 192) (hp : Dfs.StartsWith p (Dfs.oriented 164) 112) : False := by
  have hp' : Dfs.StartsWith p E112164.pre 112 := by
    intro i hi hpLen
    rw [prefix_match164 ⟨i,hi⟩]
    exact hp i hi hpLen
  let q := translate (suffix p) (0 : Vertex)
  apply E112154.region_exclusion q
  constructor
  · change vxor (0 : Vertex) ((suffix p).vertex 0) = E112154.head
    rw [E112164.suffix_head p hp',translate_head164]
  · intro v hv
    obtain ⟨i,rfl⟩ := hv
    exact translate_region164 _ (E112164.suffix_covered p hp' _ ⟨i,rfl⟩)
#print axioms entry164
end Snake9.Regrowth.Bank112
