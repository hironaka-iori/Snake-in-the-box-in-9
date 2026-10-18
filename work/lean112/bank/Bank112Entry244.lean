import E112244Data
import DfsBankData
import CubeLocal
import E112242Complete
namespace Snake9.Regrowth.Bank112
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem prefix_match244 : ∀ i : Fin 112, E112244.pre[i.val]! = (Dfs.oriented 244)[i.val]! := by decide
theorem translate_region244 : ∀ v : Vertex, v ∈ E112244.region → vxor (0 : Vertex) v ∈ E112242.region := by decide
theorem translate_head244 : vxor (0 : Vertex) E112244.head = E112242.head := by decide
theorem entry244 (p : Snake 192) (hp : Dfs.StartsWith p (Dfs.oriented 244) 112) : False := by
  have hp' : Dfs.StartsWith p E112244.pre 112 := by
    intro i hi hpLen
    rw [prefix_match244 ⟨i,hi⟩]
    exact hp i hi hpLen
  let q := translate (suffix p) (0 : Vertex)
  apply E112242.region_exclusion q
  constructor
  · change vxor (0 : Vertex) ((suffix p).vertex 0) = E112242.head
    rw [E112244.suffix_head p hp',translate_head244]
  · intro v hv
    obtain ⟨i,rfl⟩ := hv
    exact translate_region244 _ (E112244.suffix_covered p hp' _ ⟨i,rfl⟩)
#print axioms entry244
end Snake9.Regrowth.Bank112
