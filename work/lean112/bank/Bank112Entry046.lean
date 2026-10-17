import E112046Data
import DfsBankData
import CubeLocal
import E112008Complete
namespace Snake9.Regrowth.Bank112
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem prefix_match46 : ∀ i : Fin 112, E112046.pre[i.val]! = (Dfs.oriented 46)[i.val]! := by decide
theorem translate_region46 : ∀ v : Vertex, v ∈ E112046.region → vxor (0 : Vertex) v ∈ E112008.region := by decide
theorem translate_head46 : vxor (0 : Vertex) E112046.head = E112008.head := by decide
theorem entry46 (p : Snake 192) (hp : Dfs.StartsWith p (Dfs.oriented 46) 112) : False := by
  have hp' : Dfs.StartsWith p E112046.pre 112 := by
    intro i hi hpLen
    rw [prefix_match46 ⟨i,hi⟩]
    exact hp i hi hpLen
  let q := translate (suffix p) (0 : Vertex)
  apply E112008.region_exclusion q
  constructor
  · change vxor (0 : Vertex) ((suffix p).vertex 0) = E112008.head
    rw [E112046.suffix_head p hp',translate_head46]
  · intro v hv
    obtain ⟨i,rfl⟩ := hv
    exact translate_region46 _ (E112046.suffix_covered p hp' _ ⟨i,rfl⟩)
#print axioms entry46
end Snake9.Regrowth.Bank112
