import E112035Data
import DfsBankData
import CubeLocal
import E112019Complete
namespace Snake9.Regrowth.Bank112
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem prefix_match35 : ∀ i : Fin 112, E112035.pre[i.val]! = (Dfs.oriented 35)[i.val]! := by decide
theorem translate_region35 : ∀ v : Vertex, v ∈ E112035.region → vxor (0 : Vertex) v ∈ E112019.region := by decide
theorem translate_head35 : vxor (0 : Vertex) E112035.head = E112019.head := by decide
theorem entry35 (p : Snake 192) (hp : Dfs.StartsWith p (Dfs.oriented 35) 112) : False := by
  have hp' : Dfs.StartsWith p E112035.pre 112 := by
    intro i hi hpLen
    rw [prefix_match35 ⟨i,hi⟩]
    exact hp i hi hpLen
  let q := translate (suffix p) (0 : Vertex)
  apply E112019.region_exclusion q
  constructor
  · change vxor (0 : Vertex) ((suffix p).vertex 0) = E112019.head
    rw [E112035.suffix_head p hp',translate_head35]
  · intro v hv
    obtain ⟨i,rfl⟩ := hv
    exact translate_region35 _ (E112035.suffix_covered p hp' _ ⟨i,rfl⟩)
#print axioms entry35
end Snake9.Regrowth.Bank112
