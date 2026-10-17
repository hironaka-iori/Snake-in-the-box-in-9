import E112030Data
import DfsBankData
import CubeLocal
import E112026Complete
namespace Snake9.Regrowth.Bank112
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem prefix_match30 : ∀ i : Fin 112, E112030.pre[i.val]! = (Dfs.oriented 30)[i.val]! := by decide
theorem translate_region30 : ∀ v : Vertex, v ∈ E112030.region → vxor (0 : Vertex) v ∈ E112026.region := by decide
theorem translate_head30 : vxor (0 : Vertex) E112030.head = E112026.head := by decide
theorem entry30 (p : Snake 192) (hp : Dfs.StartsWith p (Dfs.oriented 30) 112) : False := by
  have hp' : Dfs.StartsWith p E112030.pre 112 := by
    intro i hi hpLen
    rw [prefix_match30 ⟨i,hi⟩]
    exact hp i hi hpLen
  let q := translate (suffix p) (0 : Vertex)
  apply E112026.region_exclusion q
  constructor
  · change vxor (0 : Vertex) ((suffix p).vertex 0) = E112026.head
    rw [E112030.suffix_head p hp',translate_head30]
  · intro v hv
    obtain ⟨i,rfl⟩ := hv
    exact translate_region30 _ (E112030.suffix_covered p hp' _ ⟨i,rfl⟩)
#print axioms entry30
end Snake9.Regrowth.Bank112
