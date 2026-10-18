import E112223Data
import DfsBankData
import CubeLocal
import E112225Complete
namespace Snake9.Regrowth.Bank112
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem prefix_match223 : ∀ i : Fin 112, E112223.pre[i.val]! = (Dfs.oriented 223)[i.val]! := by decide
theorem translate_region223 : ∀ v : Vertex, v ∈ E112223.region → vxor (0 : Vertex) v ∈ E112225.region := by decide
theorem translate_head223 : vxor (0 : Vertex) E112223.head = E112225.head := by decide
theorem entry223 (p : Snake 192) (hp : Dfs.StartsWith p (Dfs.oriented 223) 112) : False := by
  have hp' : Dfs.StartsWith p E112223.pre 112 := by
    intro i hi hpLen
    rw [prefix_match223 ⟨i,hi⟩]
    exact hp i hi hpLen
  let q := translate (suffix p) (0 : Vertex)
  apply E112225.region_exclusion q
  constructor
  · change vxor (0 : Vertex) ((suffix p).vertex 0) = E112225.head
    rw [E112223.suffix_head p hp',translate_head223]
  · intro v hv
    obtain ⟨i,rfl⟩ := hv
    exact translate_region223 _ (E112223.suffix_covered p hp' _ ⟨i,rfl⟩)
#print axioms entry223
end Snake9.Regrowth.Bank112
