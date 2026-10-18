import E112228Data
import DfsBankData
import CubeLocal
import E112098Complete
namespace Snake9.Regrowth.Bank112
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem prefix_match228 : ∀ i : Fin 112, E112228.pre[i.val]! = (Dfs.oriented 228)[i.val]! := by decide
theorem translate_region228 : ∀ v : Vertex, v ∈ E112228.region → vxor (51 : Vertex) v ∈ E112098.region := by decide
theorem translate_head228 : vxor (51 : Vertex) E112228.head = E112098.head := by decide
theorem entry228 (p : Snake 192) (hp : Dfs.StartsWith p (Dfs.oriented 228) 112) : False := by
  have hp' : Dfs.StartsWith p E112228.pre 112 := by
    intro i hi hpLen
    rw [prefix_match228 ⟨i,hi⟩]
    exact hp i hi hpLen
  let q := translate (suffix p) (51 : Vertex)
  apply E112098.region_exclusion q
  constructor
  · change vxor (51 : Vertex) ((suffix p).vertex 0) = E112098.head
    rw [E112228.suffix_head p hp',translate_head228]
  · intro v hv
    obtain ⟨i,rfl⟩ := hv
    exact translate_region228 _ (E112228.suffix_covered p hp' _ ⟨i,rfl⟩)
#print axioms entry228
end Snake9.Regrowth.Bank112
