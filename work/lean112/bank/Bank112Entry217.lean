import E112217Data
import DfsBankData
import CubeLocal
import E112213Complete
namespace Snake9.Regrowth.Bank112
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem prefix_match217 : ∀ i : Fin 112, E112217.pre[i.val]! = (Dfs.oriented 217)[i.val]! := by decide
theorem translate_region217 : ∀ v : Vertex, v ∈ E112217.region → vxor (66 : Vertex) v ∈ E112213.region := by decide
theorem translate_head217 : vxor (66 : Vertex) E112217.head = E112213.head := by decide
theorem entry217 (p : Snake 192) (hp : Dfs.StartsWith p (Dfs.oriented 217) 112) : False := by
  have hp' : Dfs.StartsWith p E112217.pre 112 := by
    intro i hi hpLen
    rw [prefix_match217 ⟨i,hi⟩]
    exact hp i hi hpLen
  let q := translate (suffix p) (66 : Vertex)
  apply E112213.region_exclusion q
  constructor
  · change vxor (66 : Vertex) ((suffix p).vertex 0) = E112213.head
    rw [E112217.suffix_head p hp',translate_head217]
  · intro v hv
    obtain ⟨i,rfl⟩ := hv
    exact translate_region217 _ (E112217.suffix_covered p hp' _ ⟨i,rfl⟩)
#print axioms entry217
end Snake9.Regrowth.Bank112
