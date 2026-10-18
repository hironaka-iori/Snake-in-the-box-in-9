import E112120Data
import DfsBankData
import CubeLocal
import E112120Complete
namespace Snake9.Regrowth.Bank112
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem prefix_match120 : ∀ i : Fin 112, E112120.pre[i.val]! = (Dfs.oriented 120)[i.val]! := by decide
theorem entry120 (p : Snake 192) (hp : Dfs.StartsWith p (Dfs.oriented 120) 112) : False := by
  have hp' : Dfs.StartsWith p E112120.pre 112 := by
    intro i hi hpLen
    rw [prefix_match120 ⟨i,hi⟩]
    exact hp i hi hpLen
  exact E112120.no192 p hp'
#print axioms entry120
end Snake9.Regrowth.Bank112
