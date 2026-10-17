import E112191Data
import DfsBankData
import CubeLocal
import E112203Complete
namespace Snake9.Regrowth.Bank112
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem prefix_match191 : ∀ i : Fin 112, E112191.pre[i.val]! = (Dfs.oriented 191)[i.val]! := by decide
theorem translate_region191 : ∀ v : Vertex, v ∈ E112191.region → vxor (320 : Vertex) v ∈ E112203.region := by decide
theorem translate_head191 : vxor (320 : Vertex) E112191.head = E112203.head := by decide
theorem entry191 (p : Snake 192) (hp : Dfs.StartsWith p (Dfs.oriented 191) 112) : False := by
  have hp' : Dfs.StartsWith p E112191.pre 112 := by
    intro i hi hpLen
    rw [prefix_match191 ⟨i,hi⟩]
    exact hp i hi hpLen
  let q := translate (suffix p) (320 : Vertex)
  apply E112203.region_exclusion q
  constructor
  · change vxor (320 : Vertex) ((suffix p).vertex 0) = E112203.head
    rw [E112191.suffix_head p hp',translate_head191]
  · intro v hv
    obtain ⟨i,rfl⟩ := hv
    exact translate_region191 _ (E112191.suffix_covered p hp' _ ⟨i,rfl⟩)
#print axioms entry191
end Snake9.Regrowth.Bank112
