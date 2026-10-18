import E112012Data
import DfsBankData
import CubeLocal
import First112Reuse
namespace Snake9.Regrowth.Bank112
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem prefix_match12 : ∀ i : Fin 112, E112012.pre[i.val]! = (Dfs.oriented 12)[i.val]! := by decide
theorem translate_region12 : ∀ v : Vertex, v ∈ E112012.region → vxor (78 : Vertex) v ∈ First112.region := by decide
theorem translate_head12 : vxor (78 : Vertex) E112012.head = First112.head := by decide
theorem entry12 (p : Snake 192) (hp : Dfs.StartsWith p (Dfs.oriented 12) 112) : False := by
  have hp' : Dfs.StartsWith p E112012.pre 112 := by
    intro i hi hpLen
    rw [prefix_match12 ⟨i,hi⟩]
    exact hp i hi hpLen
  let q := translate (suffix p) (78 : Vertex)
  apply First112.region_exclusion q
  constructor
  · change vxor (78 : Vertex) ((suffix p).vertex 0) = First112.head
    rw [E112012.suffix_head p hp',translate_head12]
  · intro v hv
    obtain ⟨i,rfl⟩ := hv
    exact translate_region12 _ (E112012.suffix_covered p hp' _ ⟨i,rfl⟩)
#print axioms entry12
end Snake9.Regrowth.Bank112
