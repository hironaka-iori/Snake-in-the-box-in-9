import E112011Data
import DfsBankData
import CubeLocal
import E112019Complete
namespace Snake9.Regrowth.Bank112
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem prefix_match11 : ∀ i : Fin 112, E112011.pre[i.val]! = (Dfs.oriented 11)[i.val]! := by decide
theorem translate_region11 : ∀ v : Vertex, v ∈ E112011.region → vxor (12 : Vertex) v ∈ E112019.region := by decide
theorem translate_head11 : vxor (12 : Vertex) E112011.head = E112019.head := by decide
theorem entry11 (p : Snake 192) (hp : Dfs.StartsWith p (Dfs.oriented 11) 112) : False := by
  have hp' : Dfs.StartsWith p E112011.pre 112 := by
    intro i hi hpLen
    rw [prefix_match11 ⟨i,hi⟩]
    exact hp i hi hpLen
  let q := translate (suffix p) (12 : Vertex)
  apply E112019.region_exclusion q
  constructor
  · change vxor (12 : Vertex) ((suffix p).vertex 0) = E112019.head
    rw [E112011.suffix_head p hp',translate_head11]
  · intro v hv
    obtain ⟨i,rfl⟩ := hv
    exact translate_region11 _ (E112011.suffix_covered p hp' _ ⟨i,rfl⟩)
#print axioms entry11
end Snake9.Regrowth.Bank112
