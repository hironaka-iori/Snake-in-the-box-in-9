import E112232Data
import DfsBankData
import CubeLocal
import E112249Complete
namespace Snake9.Regrowth.Bank112
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem prefix_match232 : ∀ i : Fin 112, E112232.pre[i.val]! = (Dfs.oriented 232)[i.val]! := by decide
theorem translate_region232 : ∀ v : Vertex, v ∈ E112232.region → vxor (472 : Vertex) v ∈ E112249.region := by decide
theorem translate_head232 : vxor (472 : Vertex) E112232.head = E112249.head := by decide
theorem entry232 (p : Snake 192) (hp : Dfs.StartsWith p (Dfs.oriented 232) 112) : False := by
  have hp' : Dfs.StartsWith p E112232.pre 112 := by
    intro i hi hpLen
    rw [prefix_match232 ⟨i,hi⟩]
    exact hp i hi hpLen
  let q := translate (suffix p) (472 : Vertex)
  apply E112249.region_exclusion q
  constructor
  · change vxor (472 : Vertex) ((suffix p).vertex 0) = E112249.head
    rw [E112232.suffix_head p hp',translate_head232]
  · intro v hv
    obtain ⟨i,rfl⟩ := hv
    exact translate_region232 _ (E112232.suffix_covered p hp' _ ⟨i,rfl⟩)
#print axioms entry232
end Snake9.Regrowth.Bank112
