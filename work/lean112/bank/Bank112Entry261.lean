import E112261Data
import DfsBankData
import CubeLocal
import E112257Complete
namespace Snake9.Regrowth.Bank112
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem prefix_match261 : ∀ i : Fin 112, E112261.pre[i.val]! = (Dfs.oriented 261)[i.val]! := by decide
theorem translate_region261 : ∀ v : Vertex, v ∈ E112261.region → vxor (24 : Vertex) v ∈ E112257.region := by decide
theorem translate_head261 : vxor (24 : Vertex) E112261.head = E112257.head := by decide
theorem entry261 (p : Snake 192) (hp : Dfs.StartsWith p (Dfs.oriented 261) 112) : False := by
  have hp' : Dfs.StartsWith p E112261.pre 112 := by
    intro i hi hpLen
    rw [prefix_match261 ⟨i,hi⟩]
    exact hp i hi hpLen
  let q := translate (suffix p) (24 : Vertex)
  apply E112257.region_exclusion q
  constructor
  · change vxor (24 : Vertex) ((suffix p).vertex 0) = E112257.head
    rw [E112261.suffix_head p hp',translate_head261]
  · intro v hv
    obtain ⟨i,rfl⟩ := hv
    exact translate_region261 _ (E112261.suffix_covered p hp' _ ⟨i,rfl⟩)
#print axioms entry261
end Snake9.Regrowth.Bank112
