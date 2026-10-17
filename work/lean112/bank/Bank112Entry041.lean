import E112041Data
import DfsBankData
import CubeLocal
import E112020Complete
namespace Snake9.Regrowth.Bank112
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem prefix_match41 : ∀ i : Fin 112, E112041.pre[i.val]! = (Dfs.oriented 41)[i.val]! := by decide
theorem translate_region41 : ∀ v : Vertex, v ∈ E112041.region → vxor (425 : Vertex) v ∈ E112020.region := by decide
theorem translate_head41 : vxor (425 : Vertex) E112041.head = E112020.head := by decide
theorem entry41 (p : Snake 192) (hp : Dfs.StartsWith p (Dfs.oriented 41) 112) : False := by
  have hp' : Dfs.StartsWith p E112041.pre 112 := by
    intro i hi hpLen
    rw [prefix_match41 ⟨i,hi⟩]
    exact hp i hi hpLen
  let q := translate (suffix p) (425 : Vertex)
  apply E112020.region_exclusion q
  constructor
  · change vxor (425 : Vertex) ((suffix p).vertex 0) = E112020.head
    rw [E112041.suffix_head p hp',translate_head41]
  · intro v hv
    obtain ⟨i,rfl⟩ := hv
    exact translate_region41 _ (E112041.suffix_covered p hp' _ ⟨i,rfl⟩)
#print axioms entry41
end Snake9.Regrowth.Bank112
