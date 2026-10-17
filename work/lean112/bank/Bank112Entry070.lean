import E112070Data
import DfsBankData
import CubeLocal
import E112081Complete
namespace Snake9.Regrowth.Bank112
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem prefix_match70 : ∀ i : Fin 112, E112070.pre[i.val]! = (Dfs.oriented 70)[i.val]! := by decide
theorem translate_region70 : ∀ v : Vertex, v ∈ E112070.region → vxor (88 : Vertex) v ∈ E112081.region := by decide
theorem translate_head70 : vxor (88 : Vertex) E112070.head = E112081.head := by decide
theorem entry70 (p : Snake 192) (hp : Dfs.StartsWith p (Dfs.oriented 70) 112) : False := by
  have hp' : Dfs.StartsWith p E112070.pre 112 := by
    intro i hi hpLen
    rw [prefix_match70 ⟨i,hi⟩]
    exact hp i hi hpLen
  let q := translate (suffix p) (88 : Vertex)
  apply E112081.region_exclusion q
  constructor
  · change vxor (88 : Vertex) ((suffix p).vertex 0) = E112081.head
    rw [E112070.suffix_head p hp',translate_head70]
  · intro v hv
    obtain ⟨i,rfl⟩ := hv
    exact translate_region70 _ (E112070.suffix_covered p hp' _ ⟨i,rfl⟩)
#print axioms entry70
end Snake9.Regrowth.Bank112
