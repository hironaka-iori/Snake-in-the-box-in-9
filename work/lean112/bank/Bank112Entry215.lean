import E112215Data
import DfsBankData
import CubeLocal
import E112213Complete
namespace Snake9.Regrowth.Bank112
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem prefix_match215 : ∀ i : Fin 112, E112215.pre[i.val]! = (Dfs.oriented 215)[i.val]! := by decide
theorem translate_region215 : ∀ v : Vertex, v ∈ E112215.region → vxor (83 : Vertex) v ∈ E112213.region := by decide
theorem translate_head215 : vxor (83 : Vertex) E112215.head = E112213.head := by decide
theorem entry215 (p : Snake 192) (hp : Dfs.StartsWith p (Dfs.oriented 215) 112) : False := by
  have hp' : Dfs.StartsWith p E112215.pre 112 := by
    intro i hi hpLen
    rw [prefix_match215 ⟨i,hi⟩]
    exact hp i hi hpLen
  let q := translate (suffix p) (83 : Vertex)
  apply E112213.region_exclusion q
  constructor
  · change vxor (83 : Vertex) ((suffix p).vertex 0) = E112213.head
    rw [E112215.suffix_head p hp',translate_head215]
  · intro v hv
    obtain ⟨i,rfl⟩ := hv
    exact translate_region215 _ (E112215.suffix_covered p hp' _ ⟨i,rfl⟩)
#print axioms entry215
end Snake9.Regrowth.Bank112
