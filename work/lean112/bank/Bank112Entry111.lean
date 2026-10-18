import E112111Data
import DfsBankData
import CubeLocal
import E112097Complete
namespace Snake9.Regrowth.Bank112
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem prefix_match111 : ∀ i : Fin 112, E112111.pre[i.val]! = (Dfs.oriented 111)[i.val]! := by decide
theorem translate_region111 : ∀ v : Vertex, v ∈ E112111.region → vxor (12 : Vertex) v ∈ E112097.region := by decide
theorem translate_head111 : vxor (12 : Vertex) E112111.head = E112097.head := by decide
theorem entry111 (p : Snake 192) (hp : Dfs.StartsWith p (Dfs.oriented 111) 112) : False := by
  have hp' : Dfs.StartsWith p E112111.pre 112 := by
    intro i hi hpLen
    rw [prefix_match111 ⟨i,hi⟩]
    exact hp i hi hpLen
  let q := translate (suffix p) (12 : Vertex)
  apply E112097.region_exclusion q
  constructor
  · change vxor (12 : Vertex) ((suffix p).vertex 0) = E112097.head
    rw [E112111.suffix_head p hp',translate_head111]
  · intro v hv
    obtain ⟨i,rfl⟩ := hv
    exact translate_region111 _ (E112111.suffix_covered p hp' _ ⟨i,rfl⟩)
#print axioms entry111
end Snake9.Regrowth.Bank112
