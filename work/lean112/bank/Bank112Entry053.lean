import E112053Data
import DfsBankData
import CubeLocal
import E112051Complete
namespace Snake9.Regrowth.Bank112
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem prefix_match53 : ∀ i : Fin 112, E112053.pre[i.val]! = (Dfs.oriented 53)[i.val]! := by decide
theorem translate_region53 : ∀ v : Vertex, v ∈ E112053.region → vxor (0 : Vertex) v ∈ E112051.region := by decide
theorem translate_head53 : vxor (0 : Vertex) E112053.head = E112051.head := by decide
theorem entry53 (p : Snake 192) (hp : Dfs.StartsWith p (Dfs.oriented 53) 112) : False := by
  have hp' : Dfs.StartsWith p E112053.pre 112 := by
    intro i hi hpLen
    rw [prefix_match53 ⟨i,hi⟩]
    exact hp i hi hpLen
  let q := translate (suffix p) (0 : Vertex)
  apply E112051.region_exclusion q
  constructor
  · change vxor (0 : Vertex) ((suffix p).vertex 0) = E112051.head
    rw [E112053.suffix_head p hp',translate_head53]
  · intro v hv
    obtain ⟨i,rfl⟩ := hv
    exact translate_region53 _ (E112053.suffix_covered p hp' _ ⟨i,rfl⟩)
#print axioms entry53
end Snake9.Regrowth.Bank112
