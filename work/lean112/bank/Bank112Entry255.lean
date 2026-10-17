import E112255Data
import DfsBankData
import CubeLocal
import E112259Complete
namespace Snake9.Regrowth.Bank112
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem prefix_match255 : ∀ i : Fin 112, E112255.pre[i.val]! = (Dfs.oriented 255)[i.val]! := by decide
theorem translate_region255 : ∀ v : Vertex, v ∈ E112255.region → vxor (24 : Vertex) v ∈ E112259.region := by decide
theorem translate_head255 : vxor (24 : Vertex) E112255.head = E112259.head := by decide
theorem entry255 (p : Snake 192) (hp : Dfs.StartsWith p (Dfs.oriented 255) 112) : False := by
  have hp' : Dfs.StartsWith p E112255.pre 112 := by
    intro i hi hpLen
    rw [prefix_match255 ⟨i,hi⟩]
    exact hp i hi hpLen
  let q := translate (suffix p) (24 : Vertex)
  apply E112259.region_exclusion q
  constructor
  · change vxor (24 : Vertex) ((suffix p).vertex 0) = E112259.head
    rw [E112255.suffix_head p hp',translate_head255]
  · intro v hv
    obtain ⟨i,rfl⟩ := hv
    exact translate_region255 _ (E112255.suffix_covered p hp' _ ⟨i,rfl⟩)
#print axioms entry255
end Snake9.Regrowth.Bank112
