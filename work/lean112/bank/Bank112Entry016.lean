import E112016Data
import DfsBankData
import CubeLocal
import First112Reuse
namespace Snake9.Regrowth.Bank112
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem prefix_match16 : ∀ i : Fin 112, E112016.pre[i.val]! = (Dfs.oriented 16)[i.val]! := by decide
theorem translate_region16 : ∀ v : Vertex, v ∈ E112016.region → vxor (66 : Vertex) v ∈ First112.region := by decide
theorem translate_head16 : vxor (66 : Vertex) E112016.head = First112.head := by decide
theorem entry16 (p : Snake 192) (hp : Dfs.StartsWith p (Dfs.oriented 16) 112) : False := by
  have hp' : Dfs.StartsWith p E112016.pre 112 := by
    intro i hi hpLen
    rw [prefix_match16 ⟨i,hi⟩]
    exact hp i hi hpLen
  let q := translate (suffix p) (66 : Vertex)
  apply First112.region_exclusion q
  constructor
  · change vxor (66 : Vertex) ((suffix p).vertex 0) = First112.head
    rw [E112016.suffix_head p hp',translate_head16]
  · intro v hv
    obtain ⟨i,rfl⟩ := hv
    exact translate_region16 _ (E112016.suffix_covered p hp' _ ⟨i,rfl⟩)
#print axioms entry16
end Snake9.Regrowth.Bank112
