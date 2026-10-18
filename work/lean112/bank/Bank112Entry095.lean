import E112095Data
import DfsBankData
import CubeLocal
import E112166Complete
namespace Snake9.Regrowth.Bank112
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem prefix_match95 : ∀ i : Fin 112, E112095.pre[i.val]! = (Dfs.oriented 95)[i.val]! := by decide
theorem translate_region95 : ∀ v : Vertex, v ∈ E112095.region → vxor (26 : Vertex) v ∈ E112166.region := by decide
theorem translate_head95 : vxor (26 : Vertex) E112095.head = E112166.head := by decide
theorem entry95 (p : Snake 192) (hp : Dfs.StartsWith p (Dfs.oriented 95) 112) : False := by
  have hp' : Dfs.StartsWith p E112095.pre 112 := by
    intro i hi hpLen
    rw [prefix_match95 ⟨i,hi⟩]
    exact hp i hi hpLen
  let q := translate (suffix p) (26 : Vertex)
  apply E112166.region_exclusion q
  constructor
  · change vxor (26 : Vertex) ((suffix p).vertex 0) = E112166.head
    rw [E112095.suffix_head p hp',translate_head95]
  · intro v hv
    obtain ⟨i,rfl⟩ := hv
    exact translate_region95 _ (E112095.suffix_covered p hp' _ ⟨i,rfl⟩)
#print axioms entry95
end Snake9.Regrowth.Bank112
