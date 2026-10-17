import E112198Data
import DfsBankData
import CubeLocal
import E112213Complete
namespace Snake9.Regrowth.Bank112
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem prefix_match198 : ∀ i : Fin 112, E112198.pre[i.val]! = (Dfs.oriented 198)[i.val]! := by decide
theorem translate_region198 : ∀ v : Vertex, v ∈ E112198.region → vxor (453 : Vertex) v ∈ E112213.region := by decide
theorem translate_head198 : vxor (453 : Vertex) E112198.head = E112213.head := by decide
theorem entry198 (p : Snake 192) (hp : Dfs.StartsWith p (Dfs.oriented 198) 112) : False := by
  have hp' : Dfs.StartsWith p E112198.pre 112 := by
    intro i hi hpLen
    rw [prefix_match198 ⟨i,hi⟩]
    exact hp i hi hpLen
  let q := translate (suffix p) (453 : Vertex)
  apply E112213.region_exclusion q
  constructor
  · change vxor (453 : Vertex) ((suffix p).vertex 0) = E112213.head
    rw [E112198.suffix_head p hp',translate_head198]
  · intro v hv
    obtain ⟨i,rfl⟩ := hv
    exact translate_region198 _ (E112198.suffix_covered p hp' _ ⟨i,rfl⟩)
#print axioms entry198
end Snake9.Regrowth.Bank112
