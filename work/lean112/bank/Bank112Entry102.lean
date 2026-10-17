import E112102Data
import DfsBankData
import CubeLocal
import E112098Complete
namespace Snake9.Regrowth.Bank112
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem prefix_match102 : ∀ i : Fin 112, E112102.pre[i.val]! = (Dfs.oriented 102)[i.val]! := by decide
theorem translate_region102 : ∀ v : Vertex, v ∈ E112102.region → vxor (0 : Vertex) v ∈ E112098.region := by decide
theorem translate_head102 : vxor (0 : Vertex) E112102.head = E112098.head := by decide
theorem entry102 (p : Snake 192) (hp : Dfs.StartsWith p (Dfs.oriented 102) 112) : False := by
  have hp' : Dfs.StartsWith p E112102.pre 112 := by
    intro i hi hpLen
    rw [prefix_match102 ⟨i,hi⟩]
    exact hp i hi hpLen
  let q := translate (suffix p) (0 : Vertex)
  apply E112098.region_exclusion q
  constructor
  · change vxor (0 : Vertex) ((suffix p).vertex 0) = E112098.head
    rw [E112102.suffix_head p hp',translate_head102]
  · intro v hv
    obtain ⟨i,rfl⟩ := hv
    exact translate_region102 _ (E112102.suffix_covered p hp' _ ⟨i,rfl⟩)
#print axioms entry102
end Snake9.Regrowth.Bank112
