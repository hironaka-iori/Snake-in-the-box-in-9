import E112018Data
import DfsBankData
import CubeLocal
import First112Reuse
namespace Snake9.Regrowth.Bank112
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem prefix_match18 : ∀ i : Fin 112, E112018.pre[i.val]! = (Dfs.oriented 18)[i.val]! := by decide
theorem translate_region18 : ∀ v : Vertex, v ∈ E112018.region → vxor (66 : Vertex) v ∈ First112.region := by decide
theorem translate_head18 : vxor (66 : Vertex) E112018.head = First112.head := by decide
theorem entry18 (p : Snake 192) (hp : Dfs.StartsWith p (Dfs.oriented 18) 112) : False := by
  have hp' : Dfs.StartsWith p E112018.pre 112 := by
    intro i hi hpLen
    rw [prefix_match18 ⟨i,hi⟩]
    exact hp i hi hpLen
  let q := translate (suffix p) (66 : Vertex)
  apply First112.region_exclusion q
  constructor
  · change vxor (66 : Vertex) ((suffix p).vertex 0) = First112.head
    rw [E112018.suffix_head p hp',translate_head18]
  · intro v hv
    obtain ⟨i,rfl⟩ := hv
    exact translate_region18 _ (E112018.suffix_covered p hp' _ ⟨i,rfl⟩)
#print axioms entry18
end Snake9.Regrowth.Bank112
