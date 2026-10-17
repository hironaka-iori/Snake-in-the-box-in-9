import E112230Data
import DfsBankData
import CubeLocal
import E112249Complete
namespace Snake9.Regrowth.Bank112
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem prefix_match230 : ∀ i : Fin 112, E112230.pre[i.val]! = (Dfs.oriented 230)[i.val]! := by decide
theorem translate_region230 : ∀ v : Vertex, v ∈ E112230.region → vxor (472 : Vertex) v ∈ E112249.region := by decide
theorem translate_head230 : vxor (472 : Vertex) E112230.head = E112249.head := by decide
theorem entry230 (p : Snake 192) (hp : Dfs.StartsWith p (Dfs.oriented 230) 112) : False := by
  have hp' : Dfs.StartsWith p E112230.pre 112 := by
    intro i hi hpLen
    rw [prefix_match230 ⟨i,hi⟩]
    exact hp i hi hpLen
  let q := translate (suffix p) (472 : Vertex)
  apply E112249.region_exclusion q
  constructor
  · change vxor (472 : Vertex) ((suffix p).vertex 0) = E112249.head
    rw [E112230.suffix_head p hp',translate_head230]
  · intro v hv
    obtain ⟨i,rfl⟩ := hv
    exact translate_region230 _ (E112230.suffix_covered p hp' _ ⟨i,rfl⟩)
#print axioms entry230
end Snake9.Regrowth.Bank112
