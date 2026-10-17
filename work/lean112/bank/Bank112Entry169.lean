import E112169Data
import DfsBankData
import CubeLocal
import E112169Complete
namespace Snake9.Regrowth.Bank112
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem prefix_match169 : ∀ i : Fin 112, E112169.pre[i.val]! = (Dfs.oriented 169)[i.val]! := by decide
theorem entry169 (p : Snake 192) (hp : Dfs.StartsWith p (Dfs.oriented 169) 112) : False := by
  have hp' : Dfs.StartsWith p E112169.pre 112 := by
    intro i hi hpLen
    rw [prefix_match169 ⟨i,hi⟩]
    exact hp i hi hpLen
  exact E112169.no192 p hp'
#print axioms entry169
end Snake9.Regrowth.Bank112
