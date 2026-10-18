import E112260Data
import DfsBankData
import CubeLocal
import E112260Complete
namespace Snake9.Regrowth.Bank112
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem prefix_match260 : ∀ i : Fin 112, E112260.pre[i.val]! = (Dfs.oriented 260)[i.val]! := by decide
theorem entry260 (p : Snake 192) (hp : Dfs.StartsWith p (Dfs.oriented 260) 112) : False := by
  have hp' : Dfs.StartsWith p E112260.pre 112 := by
    intro i hi hpLen
    rw [prefix_match260 ⟨i,hi⟩]
    exact hp i hi hpLen
  exact E112260.no192 p hp'
#print axioms entry260
end Snake9.Regrowth.Bank112
