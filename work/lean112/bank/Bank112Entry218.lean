import E112218Data
import DfsBankData
import CubeLocal
import E112098Complete
namespace Snake9.Regrowth.Bank112
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem prefix_match218 : ∀ i : Fin 112, E112218.pre[i.val]! = (Dfs.oriented 218)[i.val]! := by decide
theorem translate_region218 : ∀ v : Vertex, v ∈ E112218.region → vxor (113 : Vertex) v ∈ E112098.region := by decide
theorem translate_head218 : vxor (113 : Vertex) E112218.head = E112098.head := by decide
theorem entry218 (p : Snake 192) (hp : Dfs.StartsWith p (Dfs.oriented 218) 112) : False := by
  have hp' : Dfs.StartsWith p E112218.pre 112 := by
    intro i hi hpLen
    rw [prefix_match218 ⟨i,hi⟩]
    exact hp i hi hpLen
  let q := translate (suffix p) (113 : Vertex)
  apply E112098.region_exclusion q
  constructor
  · change vxor (113 : Vertex) ((suffix p).vertex 0) = E112098.head
    rw [E112218.suffix_head p hp',translate_head218]
  · intro v hv
    obtain ⟨i,rfl⟩ := hv
    exact translate_region218 _ (E112218.suffix_covered p hp' _ ⟨i,rfl⟩)
#print axioms entry218
end Snake9.Regrowth.Bank112
