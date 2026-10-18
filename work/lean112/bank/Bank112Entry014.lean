import E112014Data
import DfsBankData
import CubeLocal
import E112019Complete
namespace Snake9.Regrowth.Bank112
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem prefix_match14 : ∀ i : Fin 112, E112014.pre[i.val]! = (Dfs.oriented 14)[i.val]! := by decide
theorem translate_region14 : ∀ v : Vertex, v ∈ E112014.region → vxor (52 : Vertex) v ∈ E112019.region := by decide
theorem translate_head14 : vxor (52 : Vertex) E112014.head = E112019.head := by decide
theorem entry14 (p : Snake 192) (hp : Dfs.StartsWith p (Dfs.oriented 14) 112) : False := by
  have hp' : Dfs.StartsWith p E112014.pre 112 := by
    intro i hi hpLen
    rw [prefix_match14 ⟨i,hi⟩]
    exact hp i hi hpLen
  let q := translate (suffix p) (52 : Vertex)
  apply E112019.region_exclusion q
  constructor
  · change vxor (52 : Vertex) ((suffix p).vertex 0) = E112019.head
    rw [E112014.suffix_head p hp',translate_head14]
  · intro v hv
    obtain ⟨i,rfl⟩ := hv
    exact translate_region14 _ (E112014.suffix_covered p hp' _ ⟨i,rfl⟩)
#print axioms entry14
end Snake9.Regrowth.Bank112
