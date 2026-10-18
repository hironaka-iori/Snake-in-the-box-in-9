import E112069Data
import DfsBankData
import CubeLocal
import E112190Complete
namespace Snake9.Regrowth.Bank112
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem prefix_match69 : ∀ i : Fin 112, E112069.pre[i.val]! = (Dfs.oriented 69)[i.val]! := by decide
theorem translate_region69 : ∀ v : Vertex, v ∈ E112069.region → vxor (280 : Vertex) v ∈ E112190.region := by decide
theorem translate_head69 : vxor (280 : Vertex) E112069.head = E112190.head := by decide
theorem entry69 (p : Snake 192) (hp : Dfs.StartsWith p (Dfs.oriented 69) 112) : False := by
  have hp' : Dfs.StartsWith p E112069.pre 112 := by
    intro i hi hpLen
    rw [prefix_match69 ⟨i,hi⟩]
    exact hp i hi hpLen
  let q := translate (suffix p) (280 : Vertex)
  apply E112190.region_exclusion q
  constructor
  · change vxor (280 : Vertex) ((suffix p).vertex 0) = E112190.head
    rw [E112069.suffix_head p hp',translate_head69]
  · intro v hv
    obtain ⟨i,rfl⟩ := hv
    exact translate_region69 _ (E112069.suffix_covered p hp' _ ⟨i,rfl⟩)
#print axioms entry69
end Snake9.Regrowth.Bank112
