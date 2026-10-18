import E112029Data
import DfsBankData
import CubeLocal
import E112027Complete
namespace Snake9.Regrowth.Bank112
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem prefix_match29 : ∀ i : Fin 112, E112029.pre[i.val]! = (Dfs.oriented 29)[i.val]! := by decide
theorem translate_region29 : ∀ v : Vertex, v ∈ E112029.region → vxor (0 : Vertex) v ∈ E112027.region := by decide
theorem translate_head29 : vxor (0 : Vertex) E112029.head = E112027.head := by decide
theorem entry29 (p : Snake 192) (hp : Dfs.StartsWith p (Dfs.oriented 29) 112) : False := by
  have hp' : Dfs.StartsWith p E112029.pre 112 := by
    intro i hi hpLen
    rw [prefix_match29 ⟨i,hi⟩]
    exact hp i hi hpLen
  let q := translate (suffix p) (0 : Vertex)
  apply E112027.region_exclusion q
  constructor
  · change vxor (0 : Vertex) ((suffix p).vertex 0) = E112027.head
    rw [E112029.suffix_head p hp',translate_head29]
  · intro v hv
    obtain ⟨i,rfl⟩ := hv
    exact translate_region29 _ (E112029.suffix_covered p hp' _ ⟨i,rfl⟩)
#print axioms entry29
end Snake9.Regrowth.Bank112
