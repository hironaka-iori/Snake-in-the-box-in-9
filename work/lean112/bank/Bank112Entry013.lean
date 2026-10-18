import E112013Data
import DfsBankData
import CubeLocal
import E112019Complete
namespace Snake9.Regrowth.Bank112
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem prefix_match13 : ∀ i : Fin 112, E112013.pre[i.val]! = (Dfs.oriented 13)[i.val]! := by decide
theorem translate_region13 : ∀ v : Vertex, v ∈ E112013.region → vxor (12 : Vertex) v ∈ E112019.region := by decide
theorem translate_head13 : vxor (12 : Vertex) E112013.head = E112019.head := by decide
theorem entry13 (p : Snake 192) (hp : Dfs.StartsWith p (Dfs.oriented 13) 112) : False := by
  have hp' : Dfs.StartsWith p E112013.pre 112 := by
    intro i hi hpLen
    rw [prefix_match13 ⟨i,hi⟩]
    exact hp i hi hpLen
  let q := translate (suffix p) (12 : Vertex)
  apply E112019.region_exclusion q
  constructor
  · change vxor (12 : Vertex) ((suffix p).vertex 0) = E112019.head
    rw [E112013.suffix_head p hp',translate_head13]
  · intro v hv
    obtain ⟨i,rfl⟩ := hv
    exact translate_region13 _ (E112013.suffix_covered p hp' _ ⟨i,rfl⟩)
#print axioms entry13
end Snake9.Regrowth.Bank112
