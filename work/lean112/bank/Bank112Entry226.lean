import E112226Data
import DfsBankData
import CubeLocal
import E112098Complete
namespace Snake9.Regrowth.Bank112
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem prefix_match226 : ∀ i : Fin 112, E112226.pre[i.val]! = (Dfs.oriented 226)[i.val]! := by decide
theorem translate_region226 : ∀ v : Vertex, v ∈ E112226.region → vxor (51 : Vertex) v ∈ E112098.region := by decide
theorem translate_head226 : vxor (51 : Vertex) E112226.head = E112098.head := by decide
theorem entry226 (p : Snake 192) (hp : Dfs.StartsWith p (Dfs.oriented 226) 112) : False := by
  have hp' : Dfs.StartsWith p E112226.pre 112 := by
    intro i hi hpLen
    rw [prefix_match226 ⟨i,hi⟩]
    exact hp i hi hpLen
  let q := translate (suffix p) (51 : Vertex)
  apply E112098.region_exclusion q
  constructor
  · change vxor (51 : Vertex) ((suffix p).vertex 0) = E112098.head
    rw [E112226.suffix_head p hp',translate_head226]
  · intro v hv
    obtain ⟨i,rfl⟩ := hv
    exact translate_region226 _ (E112226.suffix_covered p hp' _ ⟨i,rfl⟩)
#print axioms entry226
end Snake9.Regrowth.Bank112
