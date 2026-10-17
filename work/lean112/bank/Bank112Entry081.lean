import E112081Data
import DfsBankData
import CubeLocal
import E112081Complete
namespace Snake9.Regrowth.Bank112
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem prefix_match81 : ∀ i : Fin 112, E112081.pre[i.val]! = (Dfs.oriented 81)[i.val]! := by decide
theorem entry81 (p : Snake 192) (hp : Dfs.StartsWith p (Dfs.oriented 81) 112) : False := by
  have hp' : Dfs.StartsWith p E112081.pre 112 := by
    intro i hi hpLen
    rw [prefix_match81 ⟨i,hi⟩]
    exact hp i hi hpLen
  exact E112081.no192 p hp'
#print axioms entry81
end Snake9.Regrowth.Bank112
