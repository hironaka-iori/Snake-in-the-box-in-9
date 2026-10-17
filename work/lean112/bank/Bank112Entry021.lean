import E112021Data
import DfsBankData
import CubeLocal
import E112004Complete
namespace Snake9.Regrowth.Bank112
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem prefix_match21 : ∀ i : Fin 112, E112021.pre[i.val]! = (Dfs.oriented 21)[i.val]! := by decide
theorem translate_region21 : ∀ v : Vertex, v ∈ E112021.region → vxor (361 : Vertex) v ∈ E112004.region := by decide
theorem translate_head21 : vxor (361 : Vertex) E112021.head = E112004.head := by decide
theorem entry21 (p : Snake 192) (hp : Dfs.StartsWith p (Dfs.oriented 21) 112) : False := by
  have hp' : Dfs.StartsWith p E112021.pre 112 := by
    intro i hi hpLen
    rw [prefix_match21 ⟨i,hi⟩]
    exact hp i hi hpLen
  let q := translate (suffix p) (361 : Vertex)
  apply E112004.region_exclusion q
  constructor
  · change vxor (361 : Vertex) ((suffix p).vertex 0) = E112004.head
    rw [E112021.suffix_head p hp',translate_head21]
  · intro v hv
    obtain ⟨i,rfl⟩ := hv
    exact translate_region21 _ (E112021.suffix_covered p hp' _ ⟨i,rfl⟩)
#print axioms entry21
end Snake9.Regrowth.Bank112
