import E112133Data
import DfsBankData
import CubeLocal
import E112121Complete
namespace Snake9.Regrowth.Bank112
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem prefix_match133 : ∀ i : Fin 112, E112133.pre[i.val]! = (Dfs.oriented 133)[i.val]! := by decide
theorem translate_region133 : ∀ v : Vertex, v ∈ E112133.region → vxor (0 : Vertex) v ∈ E112121.region := by decide
theorem translate_head133 : vxor (0 : Vertex) E112133.head = E112121.head := by decide
theorem entry133 (p : Snake 192) (hp : Dfs.StartsWith p (Dfs.oriented 133) 112) : False := by
  have hp' : Dfs.StartsWith p E112133.pre 112 := by
    intro i hi hpLen
    rw [prefix_match133 ⟨i,hi⟩]
    exact hp i hi hpLen
  let q := translate (suffix p) (0 : Vertex)
  apply E112121.region_exclusion q
  constructor
  · change vxor (0 : Vertex) ((suffix p).vertex 0) = E112121.head
    rw [E112133.suffix_head p hp',translate_head133]
  · intro v hv
    obtain ⟨i,rfl⟩ := hv
    exact translate_region133 _ (E112133.suffix_covered p hp' _ ⟨i,rfl⟩)
#print axioms entry133
end Snake9.Regrowth.Bank112
