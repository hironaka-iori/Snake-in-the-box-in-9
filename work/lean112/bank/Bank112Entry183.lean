import E112183Data
import DfsBankData
import CubeLocal
import E112183Complete
namespace Snake9.Regrowth.Bank112
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem prefix_match183 : ∀ i : Fin 112, E112183.pre[i.val]! = (Dfs.oriented 183)[i.val]! := by decide
theorem entry183 (p : Snake 192) (hp : Dfs.StartsWith p (Dfs.oriented 183) 112) : False := by
  have hp' : Dfs.StartsWith p E112183.pre 112 := by
    intro i hi hpLen
    rw [prefix_match183 ⟨i,hi⟩]
    exact hp i hi hpLen
  exact E112183.no192 p hp'
#print axioms entry183
end Snake9.Regrowth.Bank112
