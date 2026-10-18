import E112104Data
import DfsBankData
import CubeLocal
import E112104Complete
namespace Snake9.Regrowth.Bank112
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem prefix_match104 : ∀ i : Fin 112, E112104.pre[i.val]! = (Dfs.oriented 104)[i.val]! := by decide
theorem entry104 (p : Snake 192) (hp : Dfs.StartsWith p (Dfs.oriented 104) 112) : False := by
  have hp' : Dfs.StartsWith p E112104.pre 112 := by
    intro i hi hpLen
    rw [prefix_match104 ⟨i,hi⟩]
    exact hp i hi hpLen
  exact E112104.no192 p hp'
#print axioms entry104
end Snake9.Regrowth.Bank112
