import E112109Data
import DfsBankData
import CubeLocal
import E112107Complete
namespace Snake9.Regrowth.Bank112
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem prefix_match109 : ∀ i : Fin 112, E112109.pre[i.val]! = (Dfs.oriented 109)[i.val]! := by decide
theorem translate_region109 : ∀ v : Vertex, v ∈ E112109.region → vxor (0 : Vertex) v ∈ E112107.region := by decide
theorem translate_head109 : vxor (0 : Vertex) E112109.head = E112107.head := by decide
theorem entry109 (p : Snake 192) (hp : Dfs.StartsWith p (Dfs.oriented 109) 112) : False := by
  have hp' : Dfs.StartsWith p E112109.pre 112 := by
    intro i hi hpLen
    rw [prefix_match109 ⟨i,hi⟩]
    exact hp i hi hpLen
  let q := translate (suffix p) (0 : Vertex)
  apply E112107.region_exclusion q
  constructor
  · change vxor (0 : Vertex) ((suffix p).vertex 0) = E112107.head
    rw [E112109.suffix_head p hp',translate_head109]
  · intro v hv
    obtain ⟨i,rfl⟩ := hv
    exact translate_region109 _ (E112109.suffix_covered p hp' _ ⟨i,rfl⟩)
#print axioms entry109
end Snake9.Regrowth.Bank112
