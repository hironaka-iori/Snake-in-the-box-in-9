import E112231Data
import DfsBankData
import CubeLocal
import E112246Complete
namespace Snake9.Regrowth.Bank112
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem prefix_match231 : ∀ i : Fin 112, E112231.pre[i.val]! = (Dfs.oriented 231)[i.val]! := by decide
theorem translate_region231 : ∀ v : Vertex, v ∈ E112231.region → vxor (472 : Vertex) v ∈ E112246.region := by decide
theorem translate_head231 : vxor (472 : Vertex) E112231.head = E112246.head := by decide
theorem entry231 (p : Snake 192) (hp : Dfs.StartsWith p (Dfs.oriented 231) 112) : False := by
  have hp' : Dfs.StartsWith p E112231.pre 112 := by
    intro i hi hpLen
    rw [prefix_match231 ⟨i,hi⟩]
    exact hp i hi hpLen
  let q := translate (suffix p) (472 : Vertex)
  apply E112246.region_exclusion q
  constructor
  · change vxor (472 : Vertex) ((suffix p).vertex 0) = E112246.head
    rw [E112231.suffix_head p hp',translate_head231]
  · intro v hv
    obtain ⟨i,rfl⟩ := hv
    exact translate_region231 _ (E112231.suffix_covered p hp' _ ⟨i,rfl⟩)
#print axioms entry231
end Snake9.Regrowth.Bank112
