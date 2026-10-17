import E112200Data
import DfsBankData
import CubeLocal
import E112078Complete
namespace Snake9.Regrowth.Bank112
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem prefix_match200 : ∀ i : Fin 112, E112200.pre[i.val]! = (Dfs.oriented 200)[i.val]! := by decide
theorem translate_region200 : ∀ v : Vertex, v ∈ E112200.region → vxor (0 : Vertex) v ∈ E112078.region := by decide
theorem translate_head200 : vxor (0 : Vertex) E112200.head = E112078.head := by decide
theorem entry200 (p : Snake 192) (hp : Dfs.StartsWith p (Dfs.oriented 200) 112) : False := by
  have hp' : Dfs.StartsWith p E112200.pre 112 := by
    intro i hi hpLen
    rw [prefix_match200 ⟨i,hi⟩]
    exact hp i hi hpLen
  let q := translate (suffix p) (0 : Vertex)
  apply E112078.region_exclusion q
  constructor
  · change vxor (0 : Vertex) ((suffix p).vertex 0) = E112078.head
    rw [E112200.suffix_head p hp',translate_head200]
  · intro v hv
    obtain ⟨i,rfl⟩ := hv
    exact translate_region200 _ (E112200.suffix_covered p hp' _ ⟨i,rfl⟩)
#print axioms entry200
end Snake9.Regrowth.Bank112
