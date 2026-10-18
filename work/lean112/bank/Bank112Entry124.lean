import E112124Data
import DfsBankData
import CubeLocal
import E112120Complete
namespace Snake9.Regrowth.Bank112
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem prefix_match124 : ∀ i : Fin 112, E112124.pre[i.val]! = (Dfs.oriented 124)[i.val]! := by decide
theorem translate_region124 : ∀ v : Vertex, v ∈ E112124.region → vxor (0 : Vertex) v ∈ E112120.region := by decide
theorem translate_head124 : vxor (0 : Vertex) E112124.head = E112120.head := by decide
theorem entry124 (p : Snake 192) (hp : Dfs.StartsWith p (Dfs.oriented 124) 112) : False := by
  have hp' : Dfs.StartsWith p E112124.pre 112 := by
    intro i hi hpLen
    rw [prefix_match124 ⟨i,hi⟩]
    exact hp i hi hpLen
  let q := translate (suffix p) (0 : Vertex)
  apply E112120.region_exclusion q
  constructor
  · change vxor (0 : Vertex) ((suffix p).vertex 0) = E112120.head
    rw [E112124.suffix_head p hp',translate_head124]
  · intro v hv
    obtain ⟨i,rfl⟩ := hv
    exact translate_region124 _ (E112124.suffix_covered p hp' _ ⟨i,rfl⟩)
#print axioms entry124
end Snake9.Regrowth.Bank112
