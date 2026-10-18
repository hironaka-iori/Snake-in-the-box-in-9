import E112212Data
import DfsBankData
import CubeLocal
import E112075Complete
namespace Snake9.Regrowth.Bank112
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem prefix_match212 : ∀ i : Fin 112, E112212.pre[i.val]! = (Dfs.oriented 212)[i.val]! := by decide
theorem translate_region212 : ∀ v : Vertex, v ∈ E112212.region → vxor (261 : Vertex) v ∈ E112075.region := by decide
theorem translate_head212 : vxor (261 : Vertex) E112212.head = E112075.head := by decide
theorem entry212 (p : Snake 192) (hp : Dfs.StartsWith p (Dfs.oriented 212) 112) : False := by
  have hp' : Dfs.StartsWith p E112212.pre 112 := by
    intro i hi hpLen
    rw [prefix_match212 ⟨i,hi⟩]
    exact hp i hi hpLen
  let q := translate (suffix p) (261 : Vertex)
  apply E112075.region_exclusion q
  constructor
  · change vxor (261 : Vertex) ((suffix p).vertex 0) = E112075.head
    rw [E112212.suffix_head p hp',translate_head212]
  · intro v hv
    obtain ⟨i,rfl⟩ := hv
    exact translate_region212 _ (E112212.suffix_covered p hp' _ ⟨i,rfl⟩)
#print axioms entry212
end Snake9.Regrowth.Bank112
