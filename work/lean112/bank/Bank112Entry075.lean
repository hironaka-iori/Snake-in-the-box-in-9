import E112075Data
import DfsBankData
import CubeLocal
import E112075Complete
namespace Snake9.Regrowth.Bank112
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem prefix_match75 : ∀ i : Fin 112, E112075.pre[i.val]! = (Dfs.oriented 75)[i.val]! := by decide
theorem entry75 (p : Snake 192) (hp : Dfs.StartsWith p (Dfs.oriented 75) 112) : False := by
  have hp' : Dfs.StartsWith p E112075.pre 112 := by
    intro i hi hpLen
    rw [prefix_match75 ⟨i,hi⟩]
    exact hp i hi hpLen
  exact E112075.no192 p hp'
#print axioms entry75
end Snake9.Regrowth.Bank112
