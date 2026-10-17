import E112189Data
import DfsBankData
import CubeLocal
import E112187Complete
namespace Snake9.Regrowth.Bank112
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem prefix_match189 : ∀ i : Fin 112, E112189.pre[i.val]! = (Dfs.oriented 189)[i.val]! := by decide
theorem translate_region189 : ∀ v : Vertex, v ∈ E112189.region → vxor (0 : Vertex) v ∈ E112187.region := by decide
theorem translate_head189 : vxor (0 : Vertex) E112189.head = E112187.head := by decide
theorem entry189 (p : Snake 192) (hp : Dfs.StartsWith p (Dfs.oriented 189) 112) : False := by
  have hp' : Dfs.StartsWith p E112189.pre 112 := by
    intro i hi hpLen
    rw [prefix_match189 ⟨i,hi⟩]
    exact hp i hi hpLen
  let q := translate (suffix p) (0 : Vertex)
  apply E112187.region_exclusion q
  constructor
  · change vxor (0 : Vertex) ((suffix p).vertex 0) = E112187.head
    rw [E112189.suffix_head p hp',translate_head189]
  · intro v hv
    obtain ⟨i,rfl⟩ := hv
    exact translate_region189 _ (E112189.suffix_covered p hp' _ ⟨i,rfl⟩)
#print axioms entry189
end Snake9.Regrowth.Bank112
