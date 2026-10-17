import E112251Data
import DfsBankData
import CubeLocal
import E112242Complete
namespace Snake9.Regrowth.Bank112
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem prefix_match251 : ∀ i : Fin 112, E112251.pre[i.val]! = (Dfs.oriented 251)[i.val]! := by decide
theorem translate_region251 : ∀ v : Vertex, v ∈ E112251.region → vxor (280 : Vertex) v ∈ E112242.region := by decide
theorem translate_head251 : vxor (280 : Vertex) E112251.head = E112242.head := by decide
theorem entry251 (p : Snake 192) (hp : Dfs.StartsWith p (Dfs.oriented 251) 112) : False := by
  have hp' : Dfs.StartsWith p E112251.pre 112 := by
    intro i hi hpLen
    rw [prefix_match251 ⟨i,hi⟩]
    exact hp i hi hpLen
  let q := translate (suffix p) (280 : Vertex)
  apply E112242.region_exclusion q
  constructor
  · change vxor (280 : Vertex) ((suffix p).vertex 0) = E112242.head
    rw [E112251.suffix_head p hp',translate_head251]
  · intro v hv
    obtain ⟨i,rfl⟩ := hv
    exact translate_region251 _ (E112251.suffix_covered p hp' _ ⟨i,rfl⟩)
#print axioms entry251
end Snake9.Regrowth.Bank112
