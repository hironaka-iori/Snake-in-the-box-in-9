import E112106Data
import DfsBankData
import CubeLocal
import E112098Complete
namespace Snake9.Regrowth.Bank112
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem prefix_match106 : ∀ i : Fin 112, E112106.pre[i.val]! = (Dfs.oriented 106)[i.val]! := by decide
theorem translate_region106 : ∀ v : Vertex, v ∈ E112106.region → vxor (17 : Vertex) v ∈ E112098.region := by decide
theorem translate_head106 : vxor (17 : Vertex) E112106.head = E112098.head := by decide
theorem entry106 (p : Snake 192) (hp : Dfs.StartsWith p (Dfs.oriented 106) 112) : False := by
  have hp' : Dfs.StartsWith p E112106.pre 112 := by
    intro i hi hpLen
    rw [prefix_match106 ⟨i,hi⟩]
    exact hp i hi hpLen
  let q := translate (suffix p) (17 : Vertex)
  apply E112098.region_exclusion q
  constructor
  · change vxor (17 : Vertex) ((suffix p).vertex 0) = E112098.head
    rw [E112106.suffix_head p hp',translate_head106]
  · intro v hv
    obtain ⟨i,rfl⟩ := hv
    exact translate_region106 _ (E112106.suffix_covered p hp' _ ⟨i,rfl⟩)
#print axioms entry106
end Snake9.Regrowth.Bank112
