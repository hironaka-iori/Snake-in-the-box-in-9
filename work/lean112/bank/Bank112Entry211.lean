import E112211Data
import DfsBankData
import CubeLocal
import E112203Complete
namespace Snake9.Regrowth.Bank112
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem prefix_match211 : ∀ i : Fin 112, E112211.pre[i.val]! = (Dfs.oriented 211)[i.val]! := by decide
theorem translate_region211 : ∀ v : Vertex, v ∈ E112211.region → vxor (0 : Vertex) v ∈ E112203.region := by decide
theorem translate_head211 : vxor (0 : Vertex) E112211.head = E112203.head := by decide
theorem entry211 (p : Snake 192) (hp : Dfs.StartsWith p (Dfs.oriented 211) 112) : False := by
  have hp' : Dfs.StartsWith p E112211.pre 112 := by
    intro i hi hpLen
    rw [prefix_match211 ⟨i,hi⟩]
    exact hp i hi hpLen
  let q := translate (suffix p) (0 : Vertex)
  apply E112203.region_exclusion q
  constructor
  · change vxor (0 : Vertex) ((suffix p).vertex 0) = E112203.head
    rw [E112211.suffix_head p hp',translate_head211]
  · intro v hv
    obtain ⟨i,rfl⟩ := hv
    exact translate_region211 _ (E112211.suffix_covered p hp' _ ⟨i,rfl⟩)
#print axioms entry211
end Snake9.Regrowth.Bank112
