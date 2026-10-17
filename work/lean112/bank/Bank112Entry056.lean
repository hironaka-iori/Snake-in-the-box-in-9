import E112056Data
import DfsBankData
import CubeLocal
import E112058Complete
namespace Snake9.Regrowth.Bank112
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem prefix_match56 : ∀ i : Fin 112, E112056.pre[i.val]! = (Dfs.oriented 56)[i.val]! := by decide
theorem translate_region56 : ∀ v : Vertex, v ∈ E112056.region → vxor (85 : Vertex) v ∈ E112058.region := by decide
theorem translate_head56 : vxor (85 : Vertex) E112056.head = E112058.head := by decide
theorem entry56 (p : Snake 192) (hp : Dfs.StartsWith p (Dfs.oriented 56) 112) : False := by
  have hp' : Dfs.StartsWith p E112056.pre 112 := by
    intro i hi hpLen
    rw [prefix_match56 ⟨i,hi⟩]
    exact hp i hi hpLen
  let q := translate (suffix p) (85 : Vertex)
  apply E112058.region_exclusion q
  constructor
  · change vxor (85 : Vertex) ((suffix p).vertex 0) = E112058.head
    rw [E112056.suffix_head p hp',translate_head56]
  · intro v hv
    obtain ⟨i,rfl⟩ := hv
    exact translate_region56 _ (E112056.suffix_covered p hp' _ ⟨i,rfl⟩)
#print axioms entry56
end Snake9.Regrowth.Bank112
