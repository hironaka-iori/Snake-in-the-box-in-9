import E112019Data
import DfsBankData
import CubeLocal
import E112019Complete
namespace Snake9.Regrowth.Bank112
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem prefix_match19 : ∀ i : Fin 112, E112019.pre[i.val]! = (Dfs.oriented 19)[i.val]! := by decide
theorem entry19 (p : Snake 192) (hp : Dfs.StartsWith p (Dfs.oriented 19) 112) : False := by
  have hp' : Dfs.StartsWith p E112019.pre 112 := by
    intro i hi hpLen
    rw [prefix_match19 ⟨i,hi⟩]
    exact hp i hi hpLen
  exact E112019.no192 p hp'
#print axioms entry19
end Snake9.Regrowth.Bank112
