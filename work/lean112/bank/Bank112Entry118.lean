import E112118Data
import DfsBankData
import CubeLocal
import E112118Complete
namespace Snake9.Regrowth.Bank112
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem prefix_match118 : ∀ i : Fin 112, E112118.pre[i.val]! = (Dfs.oriented 118)[i.val]! := by decide
theorem entry118 (p : Snake 192) (hp : Dfs.StartsWith p (Dfs.oriented 118) 112) : False := by
  have hp' : Dfs.StartsWith p E112118.pre 112 := by
    intro i hi hpLen
    rw [prefix_match118 ⟨i,hi⟩]
    exact hp i hi hpLen
  exact E112118.no192 p hp'
#print axioms entry118
end Snake9.Regrowth.Bank112
