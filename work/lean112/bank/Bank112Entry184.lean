import E112184Data
import DfsBankData
import CubeLocal
import E112184Complete
namespace Snake9.Regrowth.Bank112
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem prefix_match184 : ∀ i : Fin 112, E112184.pre[i.val]! = (Dfs.oriented 184)[i.val]! := by decide
theorem entry184 (p : Snake 192) (hp : Dfs.StartsWith p (Dfs.oriented 184) 112) : False := by
  have hp' : Dfs.StartsWith p E112184.pre 112 := by
    intro i hi hpLen
    rw [prefix_match184 ⟨i,hi⟩]
    exact hp i hi hpLen
  exact E112184.no192 p hp'
#print axioms entry184
end Snake9.Regrowth.Bank112
