import E112026Data
import DfsBankData
import CubeLocal
import E112026Complete
namespace Snake9.Regrowth.Bank112
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem prefix_match26 : ∀ i : Fin 112, E112026.pre[i.val]! = (Dfs.oriented 26)[i.val]! := by decide
theorem entry26 (p : Snake 192) (hp : Dfs.StartsWith p (Dfs.oriented 26) 112) : False := by
  have hp' : Dfs.StartsWith p E112026.pre 112 := by
    intro i hi hpLen
    rw [prefix_match26 ⟨i,hi⟩]
    exact hp i hi hpLen
  exact E112026.no192 p hp'
#print axioms entry26
end Snake9.Regrowth.Bank112
