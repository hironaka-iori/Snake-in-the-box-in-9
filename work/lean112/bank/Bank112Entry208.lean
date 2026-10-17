import E112208Data
import DfsBankData
import CubeLocal
import E112190Complete
namespace Snake9.Regrowth.Bank112
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem prefix_match208 : ∀ i : Fin 112, E112208.pre[i.val]! = (Dfs.oriented 208)[i.val]! := by decide
theorem translate_region208 : ∀ v : Vertex, v ∈ E112208.region → vxor (320 : Vertex) v ∈ E112190.region := by decide
theorem translate_head208 : vxor (320 : Vertex) E112208.head = E112190.head := by decide
theorem entry208 (p : Snake 192) (hp : Dfs.StartsWith p (Dfs.oriented 208) 112) : False := by
  have hp' : Dfs.StartsWith p E112208.pre 112 := by
    intro i hi hpLen
    rw [prefix_match208 ⟨i,hi⟩]
    exact hp i hi hpLen
  let q := translate (suffix p) (320 : Vertex)
  apply E112190.region_exclusion q
  constructor
  · change vxor (320 : Vertex) ((suffix p).vertex 0) = E112190.head
    rw [E112208.suffix_head p hp',translate_head208]
  · intro v hv
    obtain ⟨i,rfl⟩ := hv
    exact translate_region208 _ (E112208.suffix_covered p hp' _ ⟨i,rfl⟩)
#print axioms entry208
end Snake9.Regrowth.Bank112
