import E112017Data
import DfsBankData
import CubeLocal
import E112019Complete
namespace Snake9.Regrowth.Bank112
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem prefix_match17 : ∀ i : Fin 112, E112017.pre[i.val]! = (Dfs.oriented 17)[i.val]! := by decide
theorem translate_region17 : ∀ v : Vertex, v ∈ E112017.region → vxor (0 : Vertex) v ∈ E112019.region := by decide
theorem translate_head17 : vxor (0 : Vertex) E112017.head = E112019.head := by decide
theorem entry17 (p : Snake 192) (hp : Dfs.StartsWith p (Dfs.oriented 17) 112) : False := by
  have hp' : Dfs.StartsWith p E112017.pre 112 := by
    intro i hi hpLen
    rw [prefix_match17 ⟨i,hi⟩]
    exact hp i hi hpLen
  let q := translate (suffix p) (0 : Vertex)
  apply E112019.region_exclusion q
  constructor
  · change vxor (0 : Vertex) ((suffix p).vertex 0) = E112019.head
    rw [E112017.suffix_head p hp',translate_head17]
  · intro v hv
    obtain ⟨i,rfl⟩ := hv
    exact translate_region17 _ (E112017.suffix_covered p hp' _ ⟨i,rfl⟩)
#print axioms entry17
end Snake9.Regrowth.Bank112
