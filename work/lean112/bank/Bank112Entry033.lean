import E112033Data
import DfsBankData
import CubeLocal
import E112019Complete
namespace Snake9.Regrowth.Bank112
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem prefix_match33 : ∀ i : Fin 112, E112033.pre[i.val]! = (Dfs.oriented 33)[i.val]! := by decide
theorem translate_region33 : ∀ v : Vertex, v ∈ E112033.region → vxor (12 : Vertex) v ∈ E112019.region := by decide
theorem translate_head33 : vxor (12 : Vertex) E112033.head = E112019.head := by decide
theorem entry33 (p : Snake 192) (hp : Dfs.StartsWith p (Dfs.oriented 33) 112) : False := by
  have hp' : Dfs.StartsWith p E112033.pre 112 := by
    intro i hi hpLen
    rw [prefix_match33 ⟨i,hi⟩]
    exact hp i hi hpLen
  let q := translate (suffix p) (12 : Vertex)
  apply E112019.region_exclusion q
  constructor
  · change vxor (12 : Vertex) ((suffix p).vertex 0) = E112019.head
    rw [E112033.suffix_head p hp',translate_head33]
  · intro v hv
    obtain ⟨i,rfl⟩ := hv
    exact translate_region33 _ (E112033.suffix_covered p hp' _ ⟨i,rfl⟩)
#print axioms entry33
end Snake9.Regrowth.Bank112
