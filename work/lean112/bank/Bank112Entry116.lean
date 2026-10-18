import E112116Data
import DfsBankData
import CubeLocal
import E112075Complete
namespace Snake9.Regrowth.Bank112
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem prefix_match116 : ∀ i : Fin 112, E112116.pre[i.val]! = (Dfs.oriented 116)[i.val]! := by decide
theorem translate_region116 : ∀ v : Vertex, v ∈ E112116.region → vxor (327 : Vertex) v ∈ E112075.region := by decide
theorem translate_head116 : vxor (327 : Vertex) E112116.head = E112075.head := by decide
theorem entry116 (p : Snake 192) (hp : Dfs.StartsWith p (Dfs.oriented 116) 112) : False := by
  have hp' : Dfs.StartsWith p E112116.pre 112 := by
    intro i hi hpLen
    rw [prefix_match116 ⟨i,hi⟩]
    exact hp i hi hpLen
  let q := translate (suffix p) (327 : Vertex)
  apply E112075.region_exclusion q
  constructor
  · change vxor (327 : Vertex) ((suffix p).vertex 0) = E112075.head
    rw [E112116.suffix_head p hp',translate_head116]
  · intro v hv
    obtain ⟨i,rfl⟩ := hv
    exact translate_region116 _ (E112116.suffix_covered p hp' _ ⟨i,rfl⟩)
#print axioms entry116
end Snake9.Regrowth.Bank112
