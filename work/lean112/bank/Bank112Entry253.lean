import E112253Data
import DfsBankData
import CubeLocal
import E112242Complete
namespace Snake9.Regrowth.Bank112
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem prefix_match253 : ∀ i : Fin 112, E112253.pre[i.val]! = (Dfs.oriented 253)[i.val]! := by decide
theorem translate_region253 : ∀ v : Vertex, v ∈ E112253.region → vxor (280 : Vertex) v ∈ E112242.region := by decide
theorem translate_head253 : vxor (280 : Vertex) E112253.head = E112242.head := by decide
theorem entry253 (p : Snake 192) (hp : Dfs.StartsWith p (Dfs.oriented 253) 112) : False := by
  have hp' : Dfs.StartsWith p E112253.pre 112 := by
    intro i hi hpLen
    rw [prefix_match253 ⟨i,hi⟩]
    exact hp i hi hpLen
  let q := translate (suffix p) (280 : Vertex)
  apply E112242.region_exclusion q
  constructor
  · change vxor (280 : Vertex) ((suffix p).vertex 0) = E112242.head
    rw [E112253.suffix_head p hp',translate_head253]
  · intro v hv
    obtain ⟨i,rfl⟩ := hv
    exact translate_region253 _ (E112253.suffix_covered p hp' _ ⟨i,rfl⟩)
#print axioms entry253
end Snake9.Regrowth.Bank112
