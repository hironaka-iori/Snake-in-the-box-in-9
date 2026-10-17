import E112247Data
import DfsBankData
import CubeLocal
import E112249Complete
namespace Snake9.Regrowth.Bank112
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem prefix_match247 : ∀ i : Fin 112, E112247.pre[i.val]! = (Dfs.oriented 247)[i.val]! := by decide
theorem translate_region247 : ∀ v : Vertex, v ∈ E112247.region → vxor (0 : Vertex) v ∈ E112249.region := by decide
theorem translate_head247 : vxor (0 : Vertex) E112247.head = E112249.head := by decide
theorem entry247 (p : Snake 192) (hp : Dfs.StartsWith p (Dfs.oriented 247) 112) : False := by
  have hp' : Dfs.StartsWith p E112247.pre 112 := by
    intro i hi hpLen
    rw [prefix_match247 ⟨i,hi⟩]
    exact hp i hi hpLen
  let q := translate (suffix p) (0 : Vertex)
  apply E112249.region_exclusion q
  constructor
  · change vxor (0 : Vertex) ((suffix p).vertex 0) = E112249.head
    rw [E112247.suffix_head p hp',translate_head247]
  · intro v hv
    obtain ⟨i,rfl⟩ := hv
    exact translate_region247 _ (E112247.suffix_covered p hp' _ ⟨i,rfl⟩)
#print axioms entry247
end Snake9.Regrowth.Bank112
