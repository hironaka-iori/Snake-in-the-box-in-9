import E112233Data
import DfsBankData
import CubeLocal
import E112246Complete
namespace Snake9.Regrowth.Bank112
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem prefix_match233 : ∀ i : Fin 112, E112233.pre[i.val]! = (Dfs.oriented 233)[i.val]! := by decide
theorem translate_region233 : ∀ v : Vertex, v ∈ E112233.region → vxor (472 : Vertex) v ∈ E112246.region := by decide
theorem translate_head233 : vxor (472 : Vertex) E112233.head = E112246.head := by decide
theorem entry233 (p : Snake 192) (hp : Dfs.StartsWith p (Dfs.oriented 233) 112) : False := by
  have hp' : Dfs.StartsWith p E112233.pre 112 := by
    intro i hi hpLen
    rw [prefix_match233 ⟨i,hi⟩]
    exact hp i hi hpLen
  let q := translate (suffix p) (472 : Vertex)
  apply E112246.region_exclusion q
  constructor
  · change vxor (472 : Vertex) ((suffix p).vertex 0) = E112246.head
    rw [E112233.suffix_head p hp',translate_head233]
  · intro v hv
    obtain ⟨i,rfl⟩ := hv
    exact translate_region233 _ (E112233.suffix_covered p hp' _ ⟨i,rfl⟩)
#print axioms entry233
end Snake9.Regrowth.Bank112
