import E112059Data
import DfsBankData
import CubeLocal
import E112057Complete
namespace Snake9.Regrowth.Bank112
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem prefix_match59 : ∀ i : Fin 112, E112059.pre[i.val]! = (Dfs.oriented 59)[i.val]! := by decide
theorem translate_region59 : ∀ v : Vertex, v ∈ E112059.region → vxor (85 : Vertex) v ∈ E112057.region := by decide
theorem translate_head59 : vxor (85 : Vertex) E112059.head = E112057.head := by decide
theorem entry59 (p : Snake 192) (hp : Dfs.StartsWith p (Dfs.oriented 59) 112) : False := by
  have hp' : Dfs.StartsWith p E112059.pre 112 := by
    intro i hi hpLen
    rw [prefix_match59 ⟨i,hi⟩]
    exact hp i hi hpLen
  let q := translate (suffix p) (85 : Vertex)
  apply E112057.region_exclusion q
  constructor
  · change vxor (85 : Vertex) ((suffix p).vertex 0) = E112057.head
    rw [E112059.suffix_head p hp',translate_head59]
  · intro v hv
    obtain ⟨i,rfl⟩ := hv
    exact translate_region59 _ (E112059.suffix_covered p hp' _ ⟨i,rfl⟩)
#print axioms entry59
end Snake9.Regrowth.Bank112
