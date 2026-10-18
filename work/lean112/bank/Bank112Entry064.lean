import E112064Data
import DfsBankData
import CubeLocal
import E112064Complete
namespace Snake9.Regrowth.Bank112
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem prefix_match64 : ∀ i : Fin 112, E112064.pre[i.val]! = (Dfs.oriented 64)[i.val]! := by decide
theorem entry64 (p : Snake 192) (hp : Dfs.StartsWith p (Dfs.oriented 64) 112) : False := by
  have hp' : Dfs.StartsWith p E112064.pre 112 := by
    intro i hi hpLen
    rw [prefix_match64 ⟨i,hi⟩]
    exact hp i hi hpLen
  exact E112064.no192 p hp'
#print axioms entry64
end Snake9.Regrowth.Bank112
