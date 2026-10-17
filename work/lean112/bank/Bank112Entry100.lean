import E112100Data
import DfsBankData
import CubeLocal
import E112096Complete
namespace Snake9.Regrowth.Bank112
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem prefix_match100 : ∀ i : Fin 112, E112100.pre[i.val]! = (Dfs.oriented 100)[i.val]! := by decide
theorem translate_region100 : ∀ v : Vertex, v ∈ E112100.region → vxor (0 : Vertex) v ∈ E112096.region := by decide
theorem translate_head100 : vxor (0 : Vertex) E112100.head = E112096.head := by decide
theorem entry100 (p : Snake 192) (hp : Dfs.StartsWith p (Dfs.oriented 100) 112) : False := by
  have hp' : Dfs.StartsWith p E112100.pre 112 := by
    intro i hi hpLen
    rw [prefix_match100 ⟨i,hi⟩]
    exact hp i hi hpLen
  let q := translate (suffix p) (0 : Vertex)
  apply E112096.region_exclusion q
  constructor
  · change vxor (0 : Vertex) ((suffix p).vertex 0) = E112096.head
    rw [E112100.suffix_head p hp',translate_head100]
  · intro v hv
    obtain ⟨i,rfl⟩ := hv
    exact translate_region100 _ (E112100.suffix_covered p hp' _ ⟨i,rfl⟩)
#print axioms entry100
end Snake9.Regrowth.Bank112
