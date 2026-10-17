import E112121Data
import DfsBankData
import CubeLocal
import E112121Complete
namespace Snake9.Regrowth.Bank112
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem prefix_match121 : ∀ i : Fin 112, E112121.pre[i.val]! = (Dfs.oriented 121)[i.val]! := by decide
theorem entry121 (p : Snake 192) (hp : Dfs.StartsWith p (Dfs.oriented 121) 112) : False := by
  have hp' : Dfs.StartsWith p E112121.pre 112 := by
    intro i hi hpLen
    rw [prefix_match121 ⟨i,hi⟩]
    exact hp i hi hpLen
  exact E112121.no192 p hp'
#print axioms entry121
end Snake9.Regrowth.Bank112
