import E112078Data
import DfsBankData
import CubeLocal
import E112078Complete
namespace Snake9.Regrowth.Bank112
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem prefix_match78 : ∀ i : Fin 112, E112078.pre[i.val]! = (Dfs.oriented 78)[i.val]! := by decide
theorem entry78 (p : Snake 192) (hp : Dfs.StartsWith p (Dfs.oriented 78) 112) : False := by
  have hp' : Dfs.StartsWith p E112078.pre 112 := by
    intro i hi hpLen
    rw [prefix_match78 ⟨i,hi⟩]
    exact hp i hi hpLen
  exact E112078.no192 p hp'
#print axioms entry78
end Snake9.Regrowth.Bank112
