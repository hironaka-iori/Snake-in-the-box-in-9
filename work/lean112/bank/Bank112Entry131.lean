import E112131Data
import DfsBankData
import CubeLocal
import E112123Complete
namespace Snake9.Regrowth.Bank112
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem prefix_match131 : ∀ i : Fin 112, E112131.pre[i.val]! = (Dfs.oriented 131)[i.val]! := by decide
theorem translate_region131 : ∀ v : Vertex, v ∈ E112131.region → vxor (0 : Vertex) v ∈ E112123.region := by decide
theorem translate_head131 : vxor (0 : Vertex) E112131.head = E112123.head := by decide
theorem entry131 (p : Snake 192) (hp : Dfs.StartsWith p (Dfs.oriented 131) 112) : False := by
  have hp' : Dfs.StartsWith p E112131.pre 112 := by
    intro i hi hpLen
    rw [prefix_match131 ⟨i,hi⟩]
    exact hp i hi hpLen
  let q := translate (suffix p) (0 : Vertex)
  apply E112123.region_exclusion q
  constructor
  · change vxor (0 : Vertex) ((suffix p).vertex 0) = E112123.head
    rw [E112131.suffix_head p hp',translate_head131]
  · intro v hv
    obtain ⟨i,rfl⟩ := hv
    exact translate_region131 _ (E112131.suffix_covered p hp' _ ⟨i,rfl⟩)
#print axioms entry131
end Snake9.Regrowth.Bank112
