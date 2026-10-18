import E112010Data
import DfsBankData
import CubeLocal
import First112Reuse
namespace Snake9.Regrowth.Bank112
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem prefix_match10 : ∀ i : Fin 112, E112010.pre[i.val]! = (Dfs.oriented 10)[i.val]! := by decide
theorem translate_region10 : ∀ v : Vertex, v ∈ E112010.region → vxor (78 : Vertex) v ∈ First112.region := by decide
theorem translate_head10 : vxor (78 : Vertex) E112010.head = First112.head := by decide
theorem entry10 (p : Snake 192) (hp : Dfs.StartsWith p (Dfs.oriented 10) 112) : False := by
  have hp' : Dfs.StartsWith p E112010.pre 112 := by
    intro i hi hpLen
    rw [prefix_match10 ⟨i,hi⟩]
    exact hp i hi hpLen
  let q := translate (suffix p) (78 : Vertex)
  apply First112.region_exclusion q
  constructor
  · change vxor (78 : Vertex) ((suffix p).vertex 0) = First112.head
    rw [E112010.suffix_head p hp',translate_head10]
  · intro v hv
    obtain ⟨i,rfl⟩ := hv
    exact translate_region10 _ (E112010.suffix_covered p hp' _ ⟨i,rfl⟩)
#print axioms entry10
end Snake9.Regrowth.Bank112
