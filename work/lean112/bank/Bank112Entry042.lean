import E112042Data
import DfsBankData
import CubeLocal
import E112020Complete
namespace Snake9.Regrowth.Bank112
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem prefix_match42 : ∀ i : Fin 112, E112042.pre[i.val]! = (Dfs.oriented 42)[i.val]! := by decide
theorem translate_region42 : ∀ v : Vertex, v ∈ E112042.region → vxor (0 : Vertex) v ∈ E112020.region := by decide
theorem translate_head42 : vxor (0 : Vertex) E112042.head = E112020.head := by decide
theorem entry42 (p : Snake 192) (hp : Dfs.StartsWith p (Dfs.oriented 42) 112) : False := by
  have hp' : Dfs.StartsWith p E112042.pre 112 := by
    intro i hi hpLen
    rw [prefix_match42 ⟨i,hi⟩]
    exact hp i hi hpLen
  let q := translate (suffix p) (0 : Vertex)
  apply E112020.region_exclusion q
  constructor
  · change vxor (0 : Vertex) ((suffix p).vertex 0) = E112020.head
    rw [E112042.suffix_head p hp',translate_head42]
  · intro v hv
    obtain ⟨i,rfl⟩ := hv
    exact translate_region42 _ (E112042.suffix_covered p hp' _ ⟨i,rfl⟩)
#print axioms entry42
end Snake9.Regrowth.Bank112
