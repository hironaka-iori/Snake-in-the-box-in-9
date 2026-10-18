import E112093Data
import DfsBankData
import CubeLocal
import E112115Complete
namespace Snake9.Regrowth.Bank112
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem prefix_match93 : ∀ i : Fin 112, E112093.pre[i.val]! = (Dfs.oriented 93)[i.val]! := by decide
theorem translate_region93 : ∀ v : Vertex, v ∈ E112093.region → vxor (83 : Vertex) v ∈ E112115.region := by decide
theorem translate_head93 : vxor (83 : Vertex) E112093.head = E112115.head := by decide
theorem entry93 (p : Snake 192) (hp : Dfs.StartsWith p (Dfs.oriented 93) 112) : False := by
  have hp' : Dfs.StartsWith p E112093.pre 112 := by
    intro i hi hpLen
    rw [prefix_match93 ⟨i,hi⟩]
    exact hp i hi hpLen
  let q := translate (suffix p) (83 : Vertex)
  apply E112115.region_exclusion q
  constructor
  · change vxor (83 : Vertex) ((suffix p).vertex 0) = E112115.head
    rw [E112093.suffix_head p hp',translate_head93]
  · intro v hv
    obtain ⟨i,rfl⟩ := hv
    exact translate_region93 _ (E112093.suffix_covered p hp' _ ⟨i,rfl⟩)
#print axioms entry93
end Snake9.Regrowth.Bank112
