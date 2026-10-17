import E112045Data
import DfsBankData
import CubeLocal
import E112040Complete
namespace Snake9.Regrowth.Bank112
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem prefix_match45 : ∀ i : Fin 112, E112045.pre[i.val]! = (Dfs.oriented 45)[i.val]! := by decide
theorem translate_region45 : ∀ v : Vertex, v ∈ E112045.region → vxor (440 : Vertex) v ∈ E112040.region := by decide
theorem translate_head45 : vxor (440 : Vertex) E112045.head = E112040.head := by decide
theorem entry45 (p : Snake 192) (hp : Dfs.StartsWith p (Dfs.oriented 45) 112) : False := by
  have hp' : Dfs.StartsWith p E112045.pre 112 := by
    intro i hi hpLen
    rw [prefix_match45 ⟨i,hi⟩]
    exact hp i hi hpLen
  let q := translate (suffix p) (440 : Vertex)
  apply E112040.region_exclusion q
  constructor
  · change vxor (440 : Vertex) ((suffix p).vertex 0) = E112040.head
    rw [E112045.suffix_head p hp',translate_head45]
  · intro v hv
    obtain ⟨i,rfl⟩ := hv
    exact translate_region45 _ (E112045.suffix_covered p hp' _ ⟨i,rfl⟩)
#print axioms entry45
end Snake9.Regrowth.Bank112
