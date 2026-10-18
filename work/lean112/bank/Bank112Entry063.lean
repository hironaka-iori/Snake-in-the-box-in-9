import E112063Data
import DfsBankData
import CubeLocal
import E112186Complete
namespace Snake9.Regrowth.Bank112
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem prefix_match63 : ∀ i : Fin 112, E112063.pre[i.val]! = (Dfs.oriented 63)[i.val]! := by decide
theorem translate_region63 : ∀ v : Vertex, v ∈ E112063.region → vxor (280 : Vertex) v ∈ E112186.region := by decide
theorem translate_head63 : vxor (280 : Vertex) E112063.head = E112186.head := by decide
theorem entry63 (p : Snake 192) (hp : Dfs.StartsWith p (Dfs.oriented 63) 112) : False := by
  have hp' : Dfs.StartsWith p E112063.pre 112 := by
    intro i hi hpLen
    rw [prefix_match63 ⟨i,hi⟩]
    exact hp i hi hpLen
  let q := translate (suffix p) (280 : Vertex)
  apply E112186.region_exclusion q
  constructor
  · change vxor (280 : Vertex) ((suffix p).vertex 0) = E112186.head
    rw [E112063.suffix_head p hp',translate_head63]
  · intro v hv
    obtain ⟨i,rfl⟩ := hv
    exact translate_region63 _ (E112063.suffix_covered p hp' _ ⟨i,rfl⟩)
#print axioms entry63
end Snake9.Regrowth.Bank112
