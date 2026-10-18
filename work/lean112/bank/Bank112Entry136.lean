import E112136Data
import DfsBankData
import CubeLocal
import E112118Complete
namespace Snake9.Regrowth.Bank112
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem prefix_match136 : ∀ i : Fin 112, E112136.pre[i.val]! = (Dfs.oriented 136)[i.val]! := by decide
theorem translate_region136 : ∀ v : Vertex, v ∈ E112136.region → vxor (0 : Vertex) v ∈ E112118.region := by decide
theorem translate_head136 : vxor (0 : Vertex) E112136.head = E112118.head := by decide
theorem entry136 (p : Snake 192) (hp : Dfs.StartsWith p (Dfs.oriented 136) 112) : False := by
  have hp' : Dfs.StartsWith p E112136.pre 112 := by
    intro i hi hpLen
    rw [prefix_match136 ⟨i,hi⟩]
    exact hp i hi hpLen
  let q := translate (suffix p) (0 : Vertex)
  apply E112118.region_exclusion q
  constructor
  · change vxor (0 : Vertex) ((suffix p).vertex 0) = E112118.head
    rw [E112136.suffix_head p hp',translate_head136]
  · intro v hv
    obtain ⟨i,rfl⟩ := hv
    exact translate_region136 _ (E112136.suffix_covered p hp' _ ⟨i,rfl⟩)
#print axioms entry136
end Snake9.Regrowth.Bank112
