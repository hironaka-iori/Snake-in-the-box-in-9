import E112165Data
import DfsBankData
import CubeLocal
import E112161Complete
namespace Snake9.Regrowth.Bank112
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem prefix_match165 : ∀ i : Fin 112, E112165.pre[i.val]! = (Dfs.oriented 165)[i.val]! := by decide
theorem translate_region165 : ∀ v : Vertex, v ∈ E112165.region → vxor (0 : Vertex) v ∈ E112161.region := by decide
theorem translate_head165 : vxor (0 : Vertex) E112165.head = E112161.head := by decide
theorem entry165 (p : Snake 192) (hp : Dfs.StartsWith p (Dfs.oriented 165) 112) : False := by
  have hp' : Dfs.StartsWith p E112165.pre 112 := by
    intro i hi hpLen
    rw [prefix_match165 ⟨i,hi⟩]
    exact hp i hi hpLen
  let q := translate (suffix p) (0 : Vertex)
  apply E112161.region_exclusion q
  constructor
  · change vxor (0 : Vertex) ((suffix p).vertex 0) = E112161.head
    rw [E112165.suffix_head p hp',translate_head165]
  · intro v hv
    obtain ⟨i,rfl⟩ := hv
    exact translate_region165 _ (E112165.suffix_covered p hp' _ ⟨i,rfl⟩)
#print axioms entry165
end Snake9.Regrowth.Bank112
