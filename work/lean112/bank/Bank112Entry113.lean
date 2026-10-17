import E112113Data
import DfsBankData
import CubeLocal
import E112097Complete
namespace Snake9.Regrowth.Bank112
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem prefix_match113 : ∀ i : Fin 112, E112113.pre[i.val]! = (Dfs.oriented 113)[i.val]! := by decide
theorem translate_region113 : ∀ v : Vertex, v ∈ E112113.region → vxor (12 : Vertex) v ∈ E112097.region := by decide
theorem translate_head113 : vxor (12 : Vertex) E112113.head = E112097.head := by decide
theorem entry113 (p : Snake 192) (hp : Dfs.StartsWith p (Dfs.oriented 113) 112) : False := by
  have hp' : Dfs.StartsWith p E112113.pre 112 := by
    intro i hi hpLen
    rw [prefix_match113 ⟨i,hi⟩]
    exact hp i hi hpLen
  let q := translate (suffix p) (12 : Vertex)
  apply E112097.region_exclusion q
  constructor
  · change vxor (12 : Vertex) ((suffix p).vertex 0) = E112097.head
    rw [E112113.suffix_head p hp',translate_head113]
  · intro v hv
    obtain ⟨i,rfl⟩ := hv
    exact translate_region113 _ (E112113.suffix_covered p hp' _ ⟨i,rfl⟩)
#print axioms entry113
end Snake9.Regrowth.Bank112
