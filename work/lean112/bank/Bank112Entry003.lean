import E112003Data
import DfsBankData
import CubeLocal
import E112019Complete
namespace Snake9.Regrowth.Bank112
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem prefix_match3 : ∀ i : Fin 112, E112003.pre[i.val]! = (Dfs.oriented 3)[i.val]! := by decide
theorem translate_region3 : ∀ v : Vertex, v ∈ E112003.region → vxor (66 : Vertex) v ∈ E112019.region := by decide
theorem translate_head3 : vxor (66 : Vertex) E112003.head = E112019.head := by decide
theorem entry3 (p : Snake 192) (hp : Dfs.StartsWith p (Dfs.oriented 3) 112) : False := by
  have hp' : Dfs.StartsWith p E112003.pre 112 := by
    intro i hi hpLen
    rw [prefix_match3 ⟨i,hi⟩]
    exact hp i hi hpLen
  let q := translate (suffix p) (66 : Vertex)
  apply E112019.region_exclusion q
  constructor
  · change vxor (66 : Vertex) ((suffix p).vertex 0) = E112019.head
    rw [E112003.suffix_head p hp',translate_head3]
  · intro v hv
    obtain ⟨i,rfl⟩ := hv
    exact translate_region3 _ (E112003.suffix_covered p hp' _ ⟨i,rfl⟩)
#print axioms entry3
end Snake9.Regrowth.Bank112
