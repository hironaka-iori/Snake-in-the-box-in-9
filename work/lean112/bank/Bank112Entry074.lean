import E112074Data
import DfsBankData
import CubeLocal
import E112115Complete
namespace Snake9.Regrowth.Bank112
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem prefix_match74 : ∀ i : Fin 112, E112074.pre[i.val]! = (Dfs.oriented 74)[i.val]! := by decide
theorem translate_region74 : ∀ v : Vertex, v ∈ E112074.region → vxor (342 : Vertex) v ∈ E112115.region := by decide
theorem translate_head74 : vxor (342 : Vertex) E112074.head = E112115.head := by decide
theorem entry74 (p : Snake 192) (hp : Dfs.StartsWith p (Dfs.oriented 74) 112) : False := by
  have hp' : Dfs.StartsWith p E112074.pre 112 := by
    intro i hi hpLen
    rw [prefix_match74 ⟨i,hi⟩]
    exact hp i hi hpLen
  let q := translate (suffix p) (342 : Vertex)
  apply E112115.region_exclusion q
  constructor
  · change vxor (342 : Vertex) ((suffix p).vertex 0) = E112115.head
    rw [E112074.suffix_head p hp',translate_head74]
  · intro v hv
    obtain ⟨i,rfl⟩ := hv
    exact translate_region74 _ (E112074.suffix_covered p hp' _ ⟨i,rfl⟩)
#print axioms entry74
end Snake9.Regrowth.Bank112
