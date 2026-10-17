import E112214Data
import DfsBankData
import CubeLocal
import E112075Complete
namespace Snake9.Regrowth.Bank112
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem prefix_match214 : ∀ i : Fin 112, E112214.pre[i.val]! = (Dfs.oriented 214)[i.val]! := by decide
theorem translate_region214 : ∀ v : Vertex, v ∈ E112214.region → vxor (342 : Vertex) v ∈ E112075.region := by decide
theorem translate_head214 : vxor (342 : Vertex) E112214.head = E112075.head := by decide
theorem entry214 (p : Snake 192) (hp : Dfs.StartsWith p (Dfs.oriented 214) 112) : False := by
  have hp' : Dfs.StartsWith p E112214.pre 112 := by
    intro i hi hpLen
    rw [prefix_match214 ⟨i,hi⟩]
    exact hp i hi hpLen
  let q := translate (suffix p) (342 : Vertex)
  apply E112075.region_exclusion q
  constructor
  · change vxor (342 : Vertex) ((suffix p).vertex 0) = E112075.head
    rw [E112214.suffix_head p hp',translate_head214]
  · intro v hv
    obtain ⟨i,rfl⟩ := hv
    exact translate_region214 _ (E112214.suffix_covered p hp' _ ⟨i,rfl⟩)
#print axioms entry214
end Snake9.Regrowth.Bank112
