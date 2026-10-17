import E112204Data
import DfsBankData
import CubeLocal
import E112078Complete
namespace Snake9.Regrowth.Bank112
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem prefix_match204 : ∀ i : Fin 112, E112204.pre[i.val]! = (Dfs.oriented 204)[i.val]! := by decide
theorem translate_region204 : ∀ v : Vertex, v ∈ E112204.region → vxor (0 : Vertex) v ∈ E112078.region := by decide
theorem translate_head204 : vxor (0 : Vertex) E112204.head = E112078.head := by decide
theorem entry204 (p : Snake 192) (hp : Dfs.StartsWith p (Dfs.oriented 204) 112) : False := by
  have hp' : Dfs.StartsWith p E112204.pre 112 := by
    intro i hi hpLen
    rw [prefix_match204 ⟨i,hi⟩]
    exact hp i hi hpLen
  let q := translate (suffix p) (0 : Vertex)
  apply E112078.region_exclusion q
  constructor
  · change vxor (0 : Vertex) ((suffix p).vertex 0) = E112078.head
    rw [E112204.suffix_head p hp',translate_head204]
  · intro v hv
    obtain ⟨i,rfl⟩ := hv
    exact translate_region204 _ (E112204.suffix_covered p hp' _ ⟨i,rfl⟩)
#print axioms entry204
end Snake9.Regrowth.Bank112
