import E112176Data
import DfsBankData
import CubeLocal
import E112174Complete
namespace Snake9.Regrowth.Bank112
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem prefix_match176 : ∀ i : Fin 112, E112176.pre[i.val]! = (Dfs.oriented 176)[i.val]! := by decide
theorem translate_region176 : ∀ v : Vertex, v ∈ E112176.region → vxor (0 : Vertex) v ∈ E112174.region := by decide
theorem translate_head176 : vxor (0 : Vertex) E112176.head = E112174.head := by decide
theorem entry176 (p : Snake 192) (hp : Dfs.StartsWith p (Dfs.oriented 176) 112) : False := by
  have hp' : Dfs.StartsWith p E112176.pre 112 := by
    intro i hi hpLen
    rw [prefix_match176 ⟨i,hi⟩]
    exact hp i hi hpLen
  let q := translate (suffix p) (0 : Vertex)
  apply E112174.region_exclusion q
  constructor
  · change vxor (0 : Vertex) ((suffix p).vertex 0) = E112174.head
    rw [E112176.suffix_head p hp',translate_head176]
  · intro v hv
    obtain ⟨i,rfl⟩ := hv
    exact translate_region176 _ (E112176.suffix_covered p hp' _ ⟨i,rfl⟩)
#print axioms entry176
end Snake9.Regrowth.Bank112
