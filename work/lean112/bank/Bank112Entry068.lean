import E112068Data
import DfsBankData
import CubeLocal
import E112081Complete
namespace Snake9.Regrowth.Bank112
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem prefix_match68 : ∀ i : Fin 112, E112068.pre[i.val]! = (Dfs.oriented 68)[i.val]! := by decide
theorem translate_region68 : ∀ v : Vertex, v ∈ E112068.region → vxor (88 : Vertex) v ∈ E112081.region := by decide
theorem translate_head68 : vxor (88 : Vertex) E112068.head = E112081.head := by decide
theorem entry68 (p : Snake 192) (hp : Dfs.StartsWith p (Dfs.oriented 68) 112) : False := by
  have hp' : Dfs.StartsWith p E112068.pre 112 := by
    intro i hi hpLen
    rw [prefix_match68 ⟨i,hi⟩]
    exact hp i hi hpLen
  let q := translate (suffix p) (88 : Vertex)
  apply E112081.region_exclusion q
  constructor
  · change vxor (88 : Vertex) ((suffix p).vertex 0) = E112081.head
    rw [E112068.suffix_head p hp',translate_head68]
  · intro v hv
    obtain ⟨i,rfl⟩ := hv
    exact translate_region68 _ (E112068.suffix_covered p hp' _ ⟨i,rfl⟩)
#print axioms entry68
end Snake9.Regrowth.Bank112
