import E112057Data
import DfsBankData
import CubeLocal
import E112057Complete
namespace Snake9.Regrowth.Bank112
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem prefix_match57 : ∀ i : Fin 112, E112057.pre[i.val]! = (Dfs.oriented 57)[i.val]! := by decide
theorem entry57 (p : Snake 192) (hp : Dfs.StartsWith p (Dfs.oriented 57) 112) : False := by
  have hp' : Dfs.StartsWith p E112057.pre 112 := by
    intro i hi hpLen
    rw [prefix_match57 ⟨i,hi⟩]
    exact hp i hi hpLen
  exact E112057.no192 p hp'
#print axioms entry57
end Snake9.Regrowth.Bank112
