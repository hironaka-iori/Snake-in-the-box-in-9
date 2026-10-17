import E112234Data
import DfsBankData
import CubeLocal
import E112234Complete
namespace Snake9.Regrowth.Bank112
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem prefix_match234 : ∀ i : Fin 112, E112234.pre[i.val]! = (Dfs.oriented 234)[i.val]! := by decide
theorem entry234 (p : Snake 192) (hp : Dfs.StartsWith p (Dfs.oriented 234) 112) : False := by
  have hp' : Dfs.StartsWith p E112234.pre 112 := by
    intro i hi hpLen
    rw [prefix_match234 ⟨i,hi⟩]
    exact hp i hi hpLen
  exact E112234.no192 p hp'
#print axioms entry234
end Snake9.Regrowth.Bank112
