import E112163Data
import DfsBankData
import CubeLocal
import E112159Complete
namespace Snake9.Regrowth.Bank112
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem prefix_match163 : ∀ i : Fin 112, E112163.pre[i.val]! = (Dfs.oriented 163)[i.val]! := by decide
theorem translate_region163 : ∀ v : Vertex, v ∈ E112163.region → vxor (0 : Vertex) v ∈ E112159.region := by decide
theorem translate_head163 : vxor (0 : Vertex) E112163.head = E112159.head := by decide
theorem entry163 (p : Snake 192) (hp : Dfs.StartsWith p (Dfs.oriented 163) 112) : False := by
  have hp' : Dfs.StartsWith p E112163.pre 112 := by
    intro i hi hpLen
    rw [prefix_match163 ⟨i,hi⟩]
    exact hp i hi hpLen
  let q := translate (suffix p) (0 : Vertex)
  apply E112159.region_exclusion q
  constructor
  · change vxor (0 : Vertex) ((suffix p).vertex 0) = E112159.head
    rw [E112163.suffix_head p hp',translate_head163]
  · intro v hv
    obtain ⟨i,rfl⟩ := hv
    exact translate_region163 _ (E112163.suffix_covered p hp' _ ⟨i,rfl⟩)
#print axioms entry163
end Snake9.Regrowth.Bank112
