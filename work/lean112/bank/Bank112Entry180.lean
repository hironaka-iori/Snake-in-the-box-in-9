import E112180Data
import DfsBankData
import CubeLocal
import E112174Complete
namespace Snake9.Regrowth.Bank112
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem prefix_match180 : ∀ i : Fin 112, E112180.pre[i.val]! = (Dfs.oriented 180)[i.val]! := by decide
theorem translate_region180 : ∀ v : Vertex, v ∈ E112180.region → vxor (0 : Vertex) v ∈ E112174.region := by decide
theorem translate_head180 : vxor (0 : Vertex) E112180.head = E112174.head := by decide
theorem entry180 (p : Snake 192) (hp : Dfs.StartsWith p (Dfs.oriented 180) 112) : False := by
  have hp' : Dfs.StartsWith p E112180.pre 112 := by
    intro i hi hpLen
    rw [prefix_match180 ⟨i,hi⟩]
    exact hp i hi hpLen
  let q := translate (suffix p) (0 : Vertex)
  apply E112174.region_exclusion q
  constructor
  · change vxor (0 : Vertex) ((suffix p).vertex 0) = E112174.head
    rw [E112180.suffix_head p hp',translate_head180]
  · intro v hv
    obtain ⟨i,rfl⟩ := hv
    exact translate_region180 _ (E112180.suffix_covered p hp' _ ⟨i,rfl⟩)
#print axioms entry180
end Snake9.Regrowth.Bank112
