import E112195Data
import DfsBankData
import CubeLocal
import E112203Complete
namespace Snake9.Regrowth.Bank112
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem prefix_match195 : ∀ i : Fin 112, E112195.pre[i.val]! = (Dfs.oriented 195)[i.val]! := by decide
theorem translate_region195 : ∀ v : Vertex, v ∈ E112195.region → vxor (320 : Vertex) v ∈ E112203.region := by decide
theorem translate_head195 : vxor (320 : Vertex) E112195.head = E112203.head := by decide
theorem entry195 (p : Snake 192) (hp : Dfs.StartsWith p (Dfs.oriented 195) 112) : False := by
  have hp' : Dfs.StartsWith p E112195.pre 112 := by
    intro i hi hpLen
    rw [prefix_match195 ⟨i,hi⟩]
    exact hp i hi hpLen
  let q := translate (suffix p) (320 : Vertex)
  apply E112203.region_exclusion q
  constructor
  · change vxor (320 : Vertex) ((suffix p).vertex 0) = E112203.head
    rw [E112195.suffix_head p hp',translate_head195]
  · intro v hv
    obtain ⟨i,rfl⟩ := hv
    exact translate_region195 _ (E112195.suffix_covered p hp' _ ⟨i,rfl⟩)
#print axioms entry195
end Snake9.Regrowth.Bank112
