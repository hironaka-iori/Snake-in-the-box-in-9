import E112103Data
import DfsBankData
import CubeLocal
import E112107Complete
namespace Snake9.Regrowth.Bank112
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem prefix_match103 : ∀ i : Fin 112, E112103.pre[i.val]! = (Dfs.oriented 103)[i.val]! := by decide
theorem translate_region103 : ∀ v : Vertex, v ∈ E112103.region → vxor (17 : Vertex) v ∈ E112107.region := by decide
theorem translate_head103 : vxor (17 : Vertex) E112103.head = E112107.head := by decide
theorem entry103 (p : Snake 192) (hp : Dfs.StartsWith p (Dfs.oriented 103) 112) : False := by
  have hp' : Dfs.StartsWith p E112103.pre 112 := by
    intro i hi hpLen
    rw [prefix_match103 ⟨i,hi⟩]
    exact hp i hi hpLen
  let q := translate (suffix p) (17 : Vertex)
  apply E112107.region_exclusion q
  constructor
  · change vxor (17 : Vertex) ((suffix p).vertex 0) = E112107.head
    rw [E112103.suffix_head p hp',translate_head103]
  · intro v hv
    obtain ⟨i,rfl⟩ := hv
    exact translate_region103 _ (E112103.suffix_covered p hp' _ ⟨i,rfl⟩)
#print axioms entry103
end Snake9.Regrowth.Bank112
