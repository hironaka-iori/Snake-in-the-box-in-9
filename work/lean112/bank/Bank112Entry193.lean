import E112193Data
import DfsBankData
import CubeLocal
import E112207Complete
namespace Snake9.Regrowth.Bank112
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem prefix_match193 : ∀ i : Fin 112, E112193.pre[i.val]! = (Dfs.oriented 193)[i.val]! := by decide
theorem translate_region193 : ∀ v : Vertex, v ∈ E112193.region → vxor (320 : Vertex) v ∈ E112207.region := by decide
theorem translate_head193 : vxor (320 : Vertex) E112193.head = E112207.head := by decide
theorem entry193 (p : Snake 192) (hp : Dfs.StartsWith p (Dfs.oriented 193) 112) : False := by
  have hp' : Dfs.StartsWith p E112193.pre 112 := by
    intro i hi hpLen
    rw [prefix_match193 ⟨i,hi⟩]
    exact hp i hi hpLen
  let q := translate (suffix p) (320 : Vertex)
  apply E112207.region_exclusion q
  constructor
  · change vxor (320 : Vertex) ((suffix p).vertex 0) = E112207.head
    rw [E112193.suffix_head p hp',translate_head193]
  · intro v hv
    obtain ⟨i,rfl⟩ := hv
    exact translate_region193 _ (E112193.suffix_covered p hp' _ ⟨i,rfl⟩)
#print axioms entry193
end Snake9.Regrowth.Bank112
