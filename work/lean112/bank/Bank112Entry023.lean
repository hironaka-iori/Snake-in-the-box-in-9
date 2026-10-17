import E112023Data
import DfsBankData
import CubeLocal
import E112004Complete
namespace Snake9.Regrowth.Bank112
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem prefix_match23 : ∀ i : Fin 112, E112023.pre[i.val]! = (Dfs.oriented 23)[i.val]! := by decide
theorem translate_region23 : ∀ v : Vertex, v ∈ E112023.region → vxor (376 : Vertex) v ∈ E112004.region := by decide
theorem translate_head23 : vxor (376 : Vertex) E112023.head = E112004.head := by decide
theorem entry23 (p : Snake 192) (hp : Dfs.StartsWith p (Dfs.oriented 23) 112) : False := by
  have hp' : Dfs.StartsWith p E112023.pre 112 := by
    intro i hi hpLen
    rw [prefix_match23 ⟨i,hi⟩]
    exact hp i hi hpLen
  let q := translate (suffix p) (376 : Vertex)
  apply E112004.region_exclusion q
  constructor
  · change vxor (376 : Vertex) ((suffix p).vertex 0) = E112004.head
    rw [E112023.suffix_head p hp',translate_head23]
  · intro v hv
    obtain ⟨i,rfl⟩ := hv
    exact translate_region23 _ (E112023.suffix_covered p hp' _ ⟨i,rfl⟩)
#print axioms entry23
end Snake9.Regrowth.Bank112
