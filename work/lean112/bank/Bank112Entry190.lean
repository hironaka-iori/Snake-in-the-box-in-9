import E112190Data
import DfsBankData
import CubeLocal
import E112190Complete
namespace Snake9.Regrowth.Bank112
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem prefix_match190 : ∀ i : Fin 112, E112190.pre[i.val]! = (Dfs.oriented 190)[i.val]! := by decide
theorem entry190 (p : Snake 192) (hp : Dfs.StartsWith p (Dfs.oriented 190) 112) : False := by
  have hp' : Dfs.StartsWith p E112190.pre 112 := by
    intro i hi hpLen
    rw [prefix_match190 ⟨i,hi⟩]
    exact hp i hi hpLen
  exact E112190.no192 p hp'
#print axioms entry190
end Snake9.Regrowth.Bank112
