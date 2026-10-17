import E112015Data
import DfsBankData
import CubeLocal
import E112034Complete
namespace Snake9.Regrowth.Bank112
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem prefix_match15 : ∀ i : Fin 112, E112015.pre[i.val]! = (Dfs.oriented 15)[i.val]! := by decide
theorem translate_region15 : ∀ v : Vertex, v ∈ E112015.region → vxor (52 : Vertex) v ∈ E112034.region := by decide
theorem translate_head15 : vxor (52 : Vertex) E112015.head = E112034.head := by decide
theorem entry15 (p : Snake 192) (hp : Dfs.StartsWith p (Dfs.oriented 15) 112) : False := by
  have hp' : Dfs.StartsWith p E112015.pre 112 := by
    intro i hi hpLen
    rw [prefix_match15 ⟨i,hi⟩]
    exact hp i hi hpLen
  let q := translate (suffix p) (52 : Vertex)
  apply E112034.region_exclusion q
  constructor
  · change vxor (52 : Vertex) ((suffix p).vertex 0) = E112034.head
    rw [E112015.suffix_head p hp',translate_head15]
  · intro v hv
    obtain ⟨i,rfl⟩ := hv
    exact translate_region15 _ (E112015.suffix_covered p hp' _ ⟨i,rfl⟩)
#print axioms entry15
end Snake9.Regrowth.Bank112
