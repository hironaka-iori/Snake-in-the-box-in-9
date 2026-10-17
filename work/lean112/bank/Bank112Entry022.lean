import E112022Data
import DfsBankData
import CubeLocal
import E112020Complete
namespace Snake9.Regrowth.Bank112
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem prefix_match22 : ∀ i : Fin 112, E112022.pre[i.val]! = (Dfs.oriented 22)[i.val]! := by decide
theorem translate_region22 : ∀ v : Vertex, v ∈ E112022.region → vxor (17 : Vertex) v ∈ E112020.region := by decide
theorem translate_head22 : vxor (17 : Vertex) E112022.head = E112020.head := by decide
theorem entry22 (p : Snake 192) (hp : Dfs.StartsWith p (Dfs.oriented 22) 112) : False := by
  have hp' : Dfs.StartsWith p E112022.pre 112 := by
    intro i hi hpLen
    rw [prefix_match22 ⟨i,hi⟩]
    exact hp i hi hpLen
  let q := translate (suffix p) (17 : Vertex)
  apply E112020.region_exclusion q
  constructor
  · change vxor (17 : Vertex) ((suffix p).vertex 0) = E112020.head
    rw [E112022.suffix_head p hp',translate_head22]
  · intro v hv
    obtain ⟨i,rfl⟩ := hv
    exact translate_region22 _ (E112022.suffix_covered p hp' _ ⟨i,rfl⟩)
#print axioms entry22
end Snake9.Regrowth.Bank112
