import E112061Data
import DfsBankData
import CubeLocal
import E112057Complete
namespace Snake9.Regrowth.Bank112
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem prefix_match61 : ∀ i : Fin 112, E112061.pre[i.val]! = (Dfs.oriented 61)[i.val]! := by decide
theorem translate_region61 : ∀ v : Vertex, v ∈ E112061.region → vxor (0 : Vertex) v ∈ E112057.region := by decide
theorem translate_head61 : vxor (0 : Vertex) E112061.head = E112057.head := by decide
theorem entry61 (p : Snake 192) (hp : Dfs.StartsWith p (Dfs.oriented 61) 112) : False := by
  have hp' : Dfs.StartsWith p E112061.pre 112 := by
    intro i hi hpLen
    rw [prefix_match61 ⟨i,hi⟩]
    exact hp i hi hpLen
  let q := translate (suffix p) (0 : Vertex)
  apply E112057.region_exclusion q
  constructor
  · change vxor (0 : Vertex) ((suffix p).vertex 0) = E112057.head
    rw [E112061.suffix_head p hp',translate_head61]
  · intro v hv
    obtain ⟨i,rfl⟩ := hv
    exact translate_region61 _ (E112061.suffix_covered p hp' _ ⟨i,rfl⟩)
#print axioms entry61
end Snake9.Regrowth.Bank112
