import E112080Data
import DfsBankData
import CubeLocal
import E112190Complete
namespace Snake9.Regrowth.Bank112
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem prefix_match80 : ∀ i : Fin 112, E112080.pre[i.val]! = (Dfs.oriented 80)[i.val]! := by decide
theorem translate_region80 : ∀ v : Vertex, v ∈ E112080.region → vxor (320 : Vertex) v ∈ E112190.region := by decide
theorem translate_head80 : vxor (320 : Vertex) E112080.head = E112190.head := by decide
theorem entry80 (p : Snake 192) (hp : Dfs.StartsWith p (Dfs.oriented 80) 112) : False := by
  have hp' : Dfs.StartsWith p E112080.pre 112 := by
    intro i hi hpLen
    rw [prefix_match80 ⟨i,hi⟩]
    exact hp i hi hpLen
  let q := translate (suffix p) (320 : Vertex)
  apply E112190.region_exclusion q
  constructor
  · change vxor (320 : Vertex) ((suffix p).vertex 0) = E112190.head
    rw [E112080.suffix_head p hp',translate_head80]
  · intro v hv
    obtain ⟨i,rfl⟩ := hv
    exact translate_region80 _ (E112080.suffix_covered p hp' _ ⟨i,rfl⟩)
#print axioms entry80
end Snake9.Regrowth.Bank112
