import E112051Data
import DfsBankData
import CubeLocal
import E112051Complete
namespace Snake9.Regrowth.Bank112
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem prefix_match51 : ∀ i : Fin 112, E112051.pre[i.val]! = (Dfs.oriented 51)[i.val]! := by decide
theorem entry51 (p : Snake 192) (hp : Dfs.StartsWith p (Dfs.oriented 51) 112) : False := by
  have hp' : Dfs.StartsWith p E112051.pre 112 := by
    intro i hi hpLen
    rw [prefix_match51 ⟨i,hi⟩]
    exact hp i hi hpLen
  exact E112051.no192 p hp'
#print axioms entry51
end Snake9.Regrowth.Bank112
