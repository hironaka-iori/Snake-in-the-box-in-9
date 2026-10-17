import E112130Data
import DfsBankData
import CubeLocal
import E112118Complete
namespace Snake9.Regrowth.Bank112
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem prefix_match130 : ∀ i : Fin 112, E112130.pre[i.val]! = (Dfs.oriented 130)[i.val]! := by decide
theorem translate_region130 : ∀ v : Vertex, v ∈ E112130.region → vxor (0 : Vertex) v ∈ E112118.region := by decide
theorem translate_head130 : vxor (0 : Vertex) E112130.head = E112118.head := by decide
theorem entry130 (p : Snake 192) (hp : Dfs.StartsWith p (Dfs.oriented 130) 112) : False := by
  have hp' : Dfs.StartsWith p E112130.pre 112 := by
    intro i hi hpLen
    rw [prefix_match130 ⟨i,hi⟩]
    exact hp i hi hpLen
  let q := translate (suffix p) (0 : Vertex)
  apply E112118.region_exclusion q
  constructor
  · change vxor (0 : Vertex) ((suffix p).vertex 0) = E112118.head
    rw [E112130.suffix_head p hp',translate_head130]
  · intro v hv
    obtain ⟨i,rfl⟩ := hv
    exact translate_region130 _ (E112130.suffix_covered p hp' _ ⟨i,rfl⟩)
#print axioms entry130
end Snake9.Regrowth.Bank112
