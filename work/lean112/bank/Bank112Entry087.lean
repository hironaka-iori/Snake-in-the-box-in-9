import E112087Data
import DfsBankData
import CubeLocal
import E112081Complete
namespace Snake9.Regrowth.Bank112
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem prefix_match87 : ∀ i : Fin 112, E112087.pre[i.val]! = (Dfs.oriented 87)[i.val]! := by decide
theorem translate_region87 : ∀ v : Vertex, v ∈ E112087.region → vxor (0 : Vertex) v ∈ E112081.region := by decide
theorem translate_head87 : vxor (0 : Vertex) E112087.head = E112081.head := by decide
theorem entry87 (p : Snake 192) (hp : Dfs.StartsWith p (Dfs.oriented 87) 112) : False := by
  have hp' : Dfs.StartsWith p E112087.pre 112 := by
    intro i hi hpLen
    rw [prefix_match87 ⟨i,hi⟩]
    exact hp i hi hpLen
  let q := translate (suffix p) (0 : Vertex)
  apply E112081.region_exclusion q
  constructor
  · change vxor (0 : Vertex) ((suffix p).vertex 0) = E112081.head
    rw [E112087.suffix_head p hp',translate_head87]
  · intro v hv
    obtain ⟨i,rfl⟩ := hv
    exact translate_region87 _ (E112087.suffix_covered p hp' _ ⟨i,rfl⟩)
#print axioms entry87
end Snake9.Regrowth.Bank112
