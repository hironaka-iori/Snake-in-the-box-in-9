import E112224Data
import DfsBankData
import CubeLocal
import E112098Complete
namespace Snake9.Regrowth.Bank112
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem prefix_match224 : ∀ i : Fin 112, E112224.pre[i.val]! = (Dfs.oriented 224)[i.val]! := by decide
theorem translate_region224 : ∀ v : Vertex, v ∈ E112224.region → vxor (63 : Vertex) v ∈ E112098.region := by decide
theorem translate_head224 : vxor (63 : Vertex) E112224.head = E112098.head := by decide
theorem entry224 (p : Snake 192) (hp : Dfs.StartsWith p (Dfs.oriented 224) 112) : False := by
  have hp' : Dfs.StartsWith p E112224.pre 112 := by
    intro i hi hpLen
    rw [prefix_match224 ⟨i,hi⟩]
    exact hp i hi hpLen
  let q := translate (suffix p) (63 : Vertex)
  apply E112098.region_exclusion q
  constructor
  · change vxor (63 : Vertex) ((suffix p).vertex 0) = E112098.head
    rw [E112224.suffix_head p hp',translate_head224]
  · intro v hv
    obtain ⟨i,rfl⟩ := hv
    exact translate_region224 _ (E112224.suffix_covered p hp' _ ⟨i,rfl⟩)
#print axioms entry224
end Snake9.Regrowth.Bank112
