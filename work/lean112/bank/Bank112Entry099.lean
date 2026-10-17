import E112099Data
import DfsBankData
import CubeLocal
import E112107Complete
namespace Snake9.Regrowth.Bank112
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem prefix_match99 : ∀ i : Fin 112, E112099.pre[i.val]! = (Dfs.oriented 99)[i.val]! := by decide
theorem translate_region99 : ∀ v : Vertex, v ∈ E112099.region → vxor (17 : Vertex) v ∈ E112107.region := by decide
theorem translate_head99 : vxor (17 : Vertex) E112099.head = E112107.head := by decide
theorem entry99 (p : Snake 192) (hp : Dfs.StartsWith p (Dfs.oriented 99) 112) : False := by
  have hp' : Dfs.StartsWith p E112099.pre 112 := by
    intro i hi hpLen
    rw [prefix_match99 ⟨i,hi⟩]
    exact hp i hi hpLen
  let q := translate (suffix p) (17 : Vertex)
  apply E112107.region_exclusion q
  constructor
  · change vxor (17 : Vertex) ((suffix p).vertex 0) = E112107.head
    rw [E112099.suffix_head p hp',translate_head99]
  · intro v hv
    obtain ⟨i,rfl⟩ := hv
    exact translate_region99 _ (E112099.suffix_covered p hp' _ ⟨i,rfl⟩)
#print axioms entry99
end Snake9.Regrowth.Bank112
