import E112025Data
import DfsBankData
import CubeLocal
import E112027Complete
namespace Snake9.Regrowth.Bank112
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem prefix_match25 : ∀ i : Fin 112, E112025.pre[i.val]! = (Dfs.oriented 25)[i.val]! := by decide
theorem translate_region25 : ∀ v : Vertex, v ∈ E112025.region → vxor (0 : Vertex) v ∈ E112027.region := by decide
theorem translate_head25 : vxor (0 : Vertex) E112025.head = E112027.head := by decide
theorem entry25 (p : Snake 192) (hp : Dfs.StartsWith p (Dfs.oriented 25) 112) : False := by
  have hp' : Dfs.StartsWith p E112025.pre 112 := by
    intro i hi hpLen
    rw [prefix_match25 ⟨i,hi⟩]
    exact hp i hi hpLen
  let q := translate (suffix p) (0 : Vertex)
  apply E112027.region_exclusion q
  constructor
  · change vxor (0 : Vertex) ((suffix p).vertex 0) = E112027.head
    rw [E112025.suffix_head p hp',translate_head25]
  · intro v hv
    obtain ⟨i,rfl⟩ := hv
    exact translate_region25 _ (E112025.suffix_covered p hp' _ ⟨i,rfl⟩)
#print axioms entry25
end Snake9.Regrowth.Bank112
