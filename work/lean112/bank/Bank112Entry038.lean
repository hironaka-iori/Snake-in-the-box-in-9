import E112038Data
import DfsBankData
import CubeLocal
import E112036Complete
namespace Snake9.Regrowth.Bank112
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem prefix_match38 : ∀ i : Fin 112, E112038.pre[i.val]! = (Dfs.oriented 38)[i.val]! := by decide
theorem translate_region38 : ∀ v : Vertex, v ∈ E112038.region → vxor (0 : Vertex) v ∈ E112036.region := by decide
theorem translate_head38 : vxor (0 : Vertex) E112038.head = E112036.head := by decide
theorem entry38 (p : Snake 192) (hp : Dfs.StartsWith p (Dfs.oriented 38) 112) : False := by
  have hp' : Dfs.StartsWith p E112038.pre 112 := by
    intro i hi hpLen
    rw [prefix_match38 ⟨i,hi⟩]
    exact hp i hi hpLen
  let q := translate (suffix p) (0 : Vertex)
  apply E112036.region_exclusion q
  constructor
  · change vxor (0 : Vertex) ((suffix p).vertex 0) = E112036.head
    rw [E112038.suffix_head p hp',translate_head38]
  · intro v hv
    obtain ⟨i,rfl⟩ := hv
    exact translate_region38 _ (E112038.suffix_covered p hp' _ ⟨i,rfl⟩)
#print axioms entry38
end Snake9.Regrowth.Bank112
