import E112252Data
import DfsBankData
import CubeLocal
import E112246Complete
namespace Snake9.Regrowth.Bank112
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem prefix_match252 : ∀ i : Fin 112, E112252.pre[i.val]! = (Dfs.oriented 252)[i.val]! := by decide
theorem translate_region252 : ∀ v : Vertex, v ∈ E112252.region → vxor (192 : Vertex) v ∈ E112246.region := by decide
theorem translate_head252 : vxor (192 : Vertex) E112252.head = E112246.head := by decide
theorem entry252 (p : Snake 192) (hp : Dfs.StartsWith p (Dfs.oriented 252) 112) : False := by
  have hp' : Dfs.StartsWith p E112252.pre 112 := by
    intro i hi hpLen
    rw [prefix_match252 ⟨i,hi⟩]
    exact hp i hi hpLen
  let q := translate (suffix p) (192 : Vertex)
  apply E112246.region_exclusion q
  constructor
  · change vxor (192 : Vertex) ((suffix p).vertex 0) = E112246.head
    rw [E112252.suffix_head p hp',translate_head252]
  · intro v hv
    obtain ⟨i,rfl⟩ := hv
    exact translate_region252 _ (E112252.suffix_covered p hp' _ ⟨i,rfl⟩)
#print axioms entry252
end Snake9.Regrowth.Bank112
