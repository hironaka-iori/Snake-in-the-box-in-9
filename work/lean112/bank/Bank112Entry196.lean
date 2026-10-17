import E112196Data
import DfsBankData
import CubeLocal
import E112190Complete
namespace Snake9.Regrowth.Bank112
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem prefix_match196 : ∀ i : Fin 112, E112196.pre[i.val]! = (Dfs.oriented 196)[i.val]! := by decide
theorem translate_region196 : ∀ v : Vertex, v ∈ E112196.region → vxor (0 : Vertex) v ∈ E112190.region := by decide
theorem translate_head196 : vxor (0 : Vertex) E112196.head = E112190.head := by decide
theorem entry196 (p : Snake 192) (hp : Dfs.StartsWith p (Dfs.oriented 196) 112) : False := by
  have hp' : Dfs.StartsWith p E112196.pre 112 := by
    intro i hi hpLen
    rw [prefix_match196 ⟨i,hi⟩]
    exact hp i hi hpLen
  let q := translate (suffix p) (0 : Vertex)
  apply E112190.region_exclusion q
  constructor
  · change vxor (0 : Vertex) ((suffix p).vertex 0) = E112190.head
    rw [E112196.suffix_head p hp',translate_head196]
  · intro v hv
    obtain ⟨i,rfl⟩ := hv
    exact translate_region196 _ (E112196.suffix_covered p hp' _ ⟨i,rfl⟩)
#print axioms entry196
end Snake9.Regrowth.Bank112
