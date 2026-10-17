import E112062Data
import DfsBankData
import CubeLocal
import E112187Complete
namespace Snake9.Regrowth.Bank112
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem prefix_match62 : ∀ i : Fin 112, E112062.pre[i.val]! = (Dfs.oriented 62)[i.val]! := by decide
theorem translate_region62 : ∀ v : Vertex, v ∈ E112062.region → vxor (280 : Vertex) v ∈ E112187.region := by decide
theorem translate_head62 : vxor (280 : Vertex) E112062.head = E112187.head := by decide
theorem entry62 (p : Snake 192) (hp : Dfs.StartsWith p (Dfs.oriented 62) 112) : False := by
  have hp' : Dfs.StartsWith p E112062.pre 112 := by
    intro i hi hpLen
    rw [prefix_match62 ⟨i,hi⟩]
    exact hp i hi hpLen
  let q := translate (suffix p) (280 : Vertex)
  apply E112187.region_exclusion q
  constructor
  · change vxor (280 : Vertex) ((suffix p).vertex 0) = E112187.head
    rw [E112062.suffix_head p hp',translate_head62]
  · intro v hv
    obtain ⟨i,rfl⟩ := hv
    exact translate_region62 _ (E112062.suffix_covered p hp' _ ⟨i,rfl⟩)
#print axioms entry62
end Snake9.Regrowth.Bank112
