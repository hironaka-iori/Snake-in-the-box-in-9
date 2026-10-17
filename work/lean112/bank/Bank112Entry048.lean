import E112048Data
import DfsBankData
import CubeLocal
import E112008Complete
namespace Snake9.Regrowth.Bank112
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem prefix_match48 : ∀ i : Fin 112, E112048.pre[i.val]! = (Dfs.oriented 48)[i.val]! := by decide
theorem translate_region48 : ∀ v : Vertex, v ∈ E112048.region → vxor (0 : Vertex) v ∈ E112008.region := by decide
theorem translate_head48 : vxor (0 : Vertex) E112048.head = E112008.head := by decide
theorem entry48 (p : Snake 192) (hp : Dfs.StartsWith p (Dfs.oriented 48) 112) : False := by
  have hp' : Dfs.StartsWith p E112048.pre 112 := by
    intro i hi hpLen
    rw [prefix_match48 ⟨i,hi⟩]
    exact hp i hi hpLen
  let q := translate (suffix p) (0 : Vertex)
  apply E112008.region_exclusion q
  constructor
  · change vxor (0 : Vertex) ((suffix p).vertex 0) = E112008.head
    rw [E112048.suffix_head p hp',translate_head48]
  · intro v hv
    obtain ⟨i,rfl⟩ := hv
    exact translate_region48 _ (E112048.suffix_covered p hp' _ ⟨i,rfl⟩)
#print axioms entry48
end Snake9.Regrowth.Bank112
