import E112192Data
import DfsBankData
import CubeLocal
import E112190Complete
namespace Snake9.Regrowth.Bank112
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem prefix_match192 : ∀ i : Fin 112, E112192.pre[i.val]! = (Dfs.oriented 192)[i.val]! := by decide
theorem translate_region192 : ∀ v : Vertex, v ∈ E112192.region → vxor (0 : Vertex) v ∈ E112190.region := by decide
theorem translate_head192 : vxor (0 : Vertex) E112192.head = E112190.head := by decide
theorem entry192 (p : Snake 192) (hp : Dfs.StartsWith p (Dfs.oriented 192) 112) : False := by
  have hp' : Dfs.StartsWith p E112192.pre 112 := by
    intro i hi hpLen
    rw [prefix_match192 ⟨i,hi⟩]
    exact hp i hi hpLen
  let q := translate (suffix p) (0 : Vertex)
  apply E112190.region_exclusion q
  constructor
  · change vxor (0 : Vertex) ((suffix p).vertex 0) = E112190.head
    rw [E112192.suffix_head p hp',translate_head192]
  · intro v hv
    obtain ⟨i,rfl⟩ := hv
    exact translate_region192 _ (E112192.suffix_covered p hp' _ ⟨i,rfl⟩)
#print axioms entry192
end Snake9.Regrowth.Bank112
