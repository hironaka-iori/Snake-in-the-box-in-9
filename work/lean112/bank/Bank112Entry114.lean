import E112114Data
import DfsBankData
import CubeLocal
import E112075Complete
namespace Snake9.Regrowth.Bank112
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem prefix_match114 : ∀ i : Fin 112, E112114.pre[i.val]! = (Dfs.oriented 114)[i.val]! := by decide
theorem translate_region114 : ∀ v : Vertex, v ∈ E112114.region → vxor (342 : Vertex) v ∈ E112075.region := by decide
theorem translate_head114 : vxor (342 : Vertex) E112114.head = E112075.head := by decide
theorem entry114 (p : Snake 192) (hp : Dfs.StartsWith p (Dfs.oriented 114) 112) : False := by
  have hp' : Dfs.StartsWith p E112114.pre 112 := by
    intro i hi hpLen
    rw [prefix_match114 ⟨i,hi⟩]
    exact hp i hi hpLen
  let q := translate (suffix p) (342 : Vertex)
  apply E112075.region_exclusion q
  constructor
  · change vxor (342 : Vertex) ((suffix p).vertex 0) = E112075.head
    rw [E112114.suffix_head p hp',translate_head114]
  · intro v hv
    obtain ⟨i,rfl⟩ := hv
    exact translate_region114 _ (E112114.suffix_covered p hp' _ ⟨i,rfl⟩)
#print axioms entry114
end Snake9.Regrowth.Bank112
