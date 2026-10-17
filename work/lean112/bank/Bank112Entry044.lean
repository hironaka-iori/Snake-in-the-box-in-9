import E112044Data
import DfsBankData
import CubeLocal
import E112020Complete
namespace Snake9.Regrowth.Bank112
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem prefix_match44 : ∀ i : Fin 112, E112044.pre[i.val]! = (Dfs.oriented 44)[i.val]! := by decide
theorem translate_region44 : ∀ v : Vertex, v ∈ E112044.region → vxor (17 : Vertex) v ∈ E112020.region := by decide
theorem translate_head44 : vxor (17 : Vertex) E112044.head = E112020.head := by decide
theorem entry44 (p : Snake 192) (hp : Dfs.StartsWith p (Dfs.oriented 44) 112) : False := by
  have hp' : Dfs.StartsWith p E112044.pre 112 := by
    intro i hi hpLen
    rw [prefix_match44 ⟨i,hi⟩]
    exact hp i hi hpLen
  let q := translate (suffix p) (17 : Vertex)
  apply E112020.region_exclusion q
  constructor
  · change vxor (17 : Vertex) ((suffix p).vertex 0) = E112020.head
    rw [E112044.suffix_head p hp',translate_head44]
  · intro v hv
    obtain ⟨i,rfl⟩ := hv
    exact translate_region44 _ (E112044.suffix_covered p hp' _ ⟨i,rfl⟩)
#print axioms entry44
end Snake9.Regrowth.Bank112
