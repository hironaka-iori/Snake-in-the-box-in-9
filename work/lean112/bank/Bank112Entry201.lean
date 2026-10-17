import E112201Data
import DfsBankData
import CubeLocal
import E112201Complete
namespace Snake9.Regrowth.Bank112
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem prefix_match201 : ∀ i : Fin 112, E112201.pre[i.val]! = (Dfs.oriented 201)[i.val]! := by decide
theorem entry201 (p : Snake 192) (hp : Dfs.StartsWith p (Dfs.oriented 201) 112) : False := by
  have hp' : Dfs.StartsWith p E112201.pre 112 := by
    intro i hi hpLen
    rw [prefix_match201 ⟨i,hi⟩]
    exact hp i hi hpLen
  exact E112201.no192 p hp'
#print axioms entry201
end Snake9.Regrowth.Bank112
