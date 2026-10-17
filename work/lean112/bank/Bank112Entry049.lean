import E112049Data
import DfsBankData
import CubeLocal
import E112047Complete
namespace Snake9.Regrowth.Bank112
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem prefix_match49 : ∀ i : Fin 112, E112049.pre[i.val]! = (Dfs.oriented 49)[i.val]! := by decide
theorem translate_region49 : ∀ v : Vertex, v ∈ E112049.region → vxor (0 : Vertex) v ∈ E112047.region := by decide
theorem translate_head49 : vxor (0 : Vertex) E112049.head = E112047.head := by decide
theorem entry49 (p : Snake 192) (hp : Dfs.StartsWith p (Dfs.oriented 49) 112) : False := by
  have hp' : Dfs.StartsWith p E112049.pre 112 := by
    intro i hi hpLen
    rw [prefix_match49 ⟨i,hi⟩]
    exact hp i hi hpLen
  let q := translate (suffix p) (0 : Vertex)
  apply E112047.region_exclusion q
  constructor
  · change vxor (0 : Vertex) ((suffix p).vertex 0) = E112047.head
    rw [E112049.suffix_head p hp',translate_head49]
  · intro v hv
    obtain ⟨i,rfl⟩ := hv
    exact translate_region49 _ (E112049.suffix_covered p hp' _ ⟨i,rfl⟩)
#print axioms entry49
end Snake9.Regrowth.Bank112
