import E112209Data
import DfsBankData
import CubeLocal
import E112207Complete
namespace Snake9.Regrowth.Bank112
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem prefix_match209 : ∀ i : Fin 112, E112209.pre[i.val]! = (Dfs.oriented 209)[i.val]! := by decide
theorem translate_region209 : ∀ v : Vertex, v ∈ E112209.region → vxor (0 : Vertex) v ∈ E112207.region := by decide
theorem translate_head209 : vxor (0 : Vertex) E112209.head = E112207.head := by decide
theorem entry209 (p : Snake 192) (hp : Dfs.StartsWith p (Dfs.oriented 209) 112) : False := by
  have hp' : Dfs.StartsWith p E112209.pre 112 := by
    intro i hi hpLen
    rw [prefix_match209 ⟨i,hi⟩]
    exact hp i hi hpLen
  let q := translate (suffix p) (0 : Vertex)
  apply E112207.region_exclusion q
  constructor
  · change vxor (0 : Vertex) ((suffix p).vertex 0) = E112207.head
    rw [E112209.suffix_head p hp',translate_head209]
  · intro v hv
    obtain ⟨i,rfl⟩ := hv
    exact translate_region209 _ (E112209.suffix_covered p hp' _ ⟨i,rfl⟩)
#print axioms entry209
end Snake9.Regrowth.Bank112
