import E112002Data
import DfsBankData
import CubeLocal
import First112Reuse
namespace Snake9.Regrowth.Bank112
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem prefix_match2 : ∀ i : Fin 112, E112002.pre[i.val]! = (Dfs.oriented 2)[i.val]! := by decide
theorem translate_region2 : ∀ v : Vertex, v ∈ E112002.region → vxor (0 : Vertex) v ∈ First112.region := by decide
theorem translate_head2 : vxor (0 : Vertex) E112002.head = First112.head := by decide
theorem entry2 (p : Snake 192) (hp : Dfs.StartsWith p (Dfs.oriented 2) 112) : False := by
  have hp' : Dfs.StartsWith p E112002.pre 112 := by
    intro i hi hpLen
    rw [prefix_match2 ⟨i,hi⟩]
    exact hp i hi hpLen
  let q := translate (suffix p) (0 : Vertex)
  apply First112.region_exclusion q
  constructor
  · change vxor (0 : Vertex) ((suffix p).vertex 0) = First112.head
    rw [E112002.suffix_head p hp',translate_head2]
  · intro v hv
    obtain ⟨i,rfl⟩ := hv
    exact translate_region2 _ (E112002.suffix_covered p hp' _ ⟨i,rfl⟩)
#print axioms entry2
end Snake9.Regrowth.Bank112
