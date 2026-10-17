import E112227Data
import DfsBankData
import CubeLocal
import E112225Complete
namespace Snake9.Regrowth.Bank112
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem prefix_match227 : ∀ i : Fin 112, E112227.pre[i.val]! = (Dfs.oriented 227)[i.val]! := by decide
theorem translate_region227 : ∀ v : Vertex, v ∈ E112227.region → vxor (12 : Vertex) v ∈ E112225.region := by decide
theorem translate_head227 : vxor (12 : Vertex) E112227.head = E112225.head := by decide
theorem entry227 (p : Snake 192) (hp : Dfs.StartsWith p (Dfs.oriented 227) 112) : False := by
  have hp' : Dfs.StartsWith p E112227.pre 112 := by
    intro i hi hpLen
    rw [prefix_match227 ⟨i,hi⟩]
    exact hp i hi hpLen
  let q := translate (suffix p) (12 : Vertex)
  apply E112225.region_exclusion q
  constructor
  · change vxor (12 : Vertex) ((suffix p).vertex 0) = E112225.head
    rw [E112227.suffix_head p hp',translate_head227]
  · intro v hv
    obtain ⟨i,rfl⟩ := hv
    exact translate_region227 _ (E112227.suffix_covered p hp' _ ⟨i,rfl⟩)
#print axioms entry227
end Snake9.Regrowth.Bank112
