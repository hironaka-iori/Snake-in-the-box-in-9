import E112060Data
import DfsBankData
import CubeLocal
import E112058Complete
namespace Snake9.Regrowth.Bank112
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem prefix_match60 : ∀ i : Fin 112, E112060.pre[i.val]! = (Dfs.oriented 60)[i.val]! := by decide
theorem translate_region60 : ∀ v : Vertex, v ∈ E112060.region → vxor (85 : Vertex) v ∈ E112058.region := by decide
theorem translate_head60 : vxor (85 : Vertex) E112060.head = E112058.head := by decide
theorem entry60 (p : Snake 192) (hp : Dfs.StartsWith p (Dfs.oriented 60) 112) : False := by
  have hp' : Dfs.StartsWith p E112060.pre 112 := by
    intro i hi hpLen
    rw [prefix_match60 ⟨i,hi⟩]
    exact hp i hi hpLen
  let q := translate (suffix p) (85 : Vertex)
  apply E112058.region_exclusion q
  constructor
  · change vxor (85 : Vertex) ((suffix p).vertex 0) = E112058.head
    rw [E112060.suffix_head p hp',translate_head60]
  · intro v hv
    obtain ⟨i,rfl⟩ := hv
    exact translate_region60 _ (E112060.suffix_covered p hp' _ ⟨i,rfl⟩)
#print axioms entry60
end Snake9.Regrowth.Bank112
