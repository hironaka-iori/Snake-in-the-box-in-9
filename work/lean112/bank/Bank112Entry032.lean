import E112032Data
import DfsBankData
import CubeLocal
import E112034Complete
namespace Snake9.Regrowth.Bank112
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem prefix_match32 : ∀ i : Fin 112, E112032.pre[i.val]! = (Dfs.oriented 32)[i.val]! := by decide
theorem translate_region32 : ∀ v : Vertex, v ∈ E112032.region → vxor (12 : Vertex) v ∈ E112034.region := by decide
theorem translate_head32 : vxor (12 : Vertex) E112032.head = E112034.head := by decide
theorem entry32 (p : Snake 192) (hp : Dfs.StartsWith p (Dfs.oriented 32) 112) : False := by
  have hp' : Dfs.StartsWith p E112032.pre 112 := by
    intro i hi hpLen
    rw [prefix_match32 ⟨i,hi⟩]
    exact hp i hi hpLen
  let q := translate (suffix p) (12 : Vertex)
  apply E112034.region_exclusion q
  constructor
  · change vxor (12 : Vertex) ((suffix p).vertex 0) = E112034.head
    rw [E112032.suffix_head p hp',translate_head32]
  · intro v hv
    obtain ⟨i,rfl⟩ := hv
    exact translate_region32 _ (E112032.suffix_covered p hp' _ ⟨i,rfl⟩)
#print axioms entry32
end Snake9.Regrowth.Bank112
