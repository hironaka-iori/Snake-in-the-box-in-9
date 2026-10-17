import E112162Data
import DfsBankData
import CubeLocal
import E112158Complete
namespace Snake9.Regrowth.Bank112
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem prefix_match162 : ∀ i : Fin 112, E112162.pre[i.val]! = (Dfs.oriented 162)[i.val]! := by decide
theorem translate_region162 : ∀ v : Vertex, v ∈ E112162.region → vxor (0 : Vertex) v ∈ E112158.region := by decide
theorem translate_head162 : vxor (0 : Vertex) E112162.head = E112158.head := by decide
theorem entry162 (p : Snake 192) (hp : Dfs.StartsWith p (Dfs.oriented 162) 112) : False := by
  have hp' : Dfs.StartsWith p E112162.pre 112 := by
    intro i hi hpLen
    rw [prefix_match162 ⟨i,hi⟩]
    exact hp i hi hpLen
  let q := translate (suffix p) (0 : Vertex)
  apply E112158.region_exclusion q
  constructor
  · change vxor (0 : Vertex) ((suffix p).vertex 0) = E112158.head
    rw [E112162.suffix_head p hp',translate_head162]
  · intro v hv
    obtain ⟨i,rfl⟩ := hv
    exact translate_region162 _ (E112162.suffix_covered p hp' _ ⟨i,rfl⟩)
#print axioms entry162
end Snake9.Regrowth.Bank112
