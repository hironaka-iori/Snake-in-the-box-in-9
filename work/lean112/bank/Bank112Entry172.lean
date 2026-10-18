import E112172Data
import DfsBankData
import CubeLocal
import E112166Complete
namespace Snake9.Regrowth.Bank112
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem prefix_match172 : ∀ i : Fin 112, E112172.pre[i.val]! = (Dfs.oriented 172)[i.val]! := by decide
theorem translate_region172 : ∀ v : Vertex, v ∈ E112172.region → vxor (12 : Vertex) v ∈ E112166.region := by decide
theorem translate_head172 : vxor (12 : Vertex) E112172.head = E112166.head := by decide
theorem entry172 (p : Snake 192) (hp : Dfs.StartsWith p (Dfs.oriented 172) 112) : False := by
  have hp' : Dfs.StartsWith p E112172.pre 112 := by
    intro i hi hpLen
    rw [prefix_match172 ⟨i,hi⟩]
    exact hp i hi hpLen
  let q := translate (suffix p) (12 : Vertex)
  apply E112166.region_exclusion q
  constructor
  · change vxor (12 : Vertex) ((suffix p).vertex 0) = E112166.head
    rw [E112172.suffix_head p hp',translate_head172]
  · intro v hv
    obtain ⟨i,rfl⟩ := hv
    exact translate_region172 _ (E112172.suffix_covered p hp' _ ⟨i,rfl⟩)
#print axioms entry172
end Snake9.Regrowth.Bank112
