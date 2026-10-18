import E112181Data
import DfsBankData
import CubeLocal
import E112179Complete
namespace Snake9.Regrowth.Bank112
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem prefix_match181 : ∀ i : Fin 112, E112181.pre[i.val]! = (Dfs.oriented 181)[i.val]! := by decide
theorem translate_region181 : ∀ v : Vertex, v ∈ E112181.region → vxor (0 : Vertex) v ∈ E112179.region := by decide
theorem translate_head181 : vxor (0 : Vertex) E112181.head = E112179.head := by decide
theorem entry181 (p : Snake 192) (hp : Dfs.StartsWith p (Dfs.oriented 181) 112) : False := by
  have hp' : Dfs.StartsWith p E112181.pre 112 := by
    intro i hi hpLen
    rw [prefix_match181 ⟨i,hi⟩]
    exact hp i hi hpLen
  let q := translate (suffix p) (0 : Vertex)
  apply E112179.region_exclusion q
  constructor
  · change vxor (0 : Vertex) ((suffix p).vertex 0) = E112179.head
    rw [E112181.suffix_head p hp',translate_head181]
  · intro v hv
    obtain ⟨i,rfl⟩ := hv
    exact translate_region181 _ (E112181.suffix_covered p hp' _ ⟨i,rfl⟩)
#print axioms entry181
end Snake9.Regrowth.Bank112
