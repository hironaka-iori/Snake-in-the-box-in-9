import E112161Data
import DfsBankData
import CubeLocal
import E112161Complete
namespace Snake9.Regrowth.Bank112
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem prefix_match161 : ∀ i : Fin 112, E112161.pre[i.val]! = (Dfs.oriented 161)[i.val]! := by decide
theorem entry161 (p : Snake 192) (hp : Dfs.StartsWith p (Dfs.oriented 161) 112) : False := by
  have hp' : Dfs.StartsWith p E112161.pre 112 := by
    intro i hi hpLen
    rw [prefix_match161 ⟨i,hi⟩]
    exact hp i hi hpLen
  exact E112161.no192 p hp'
#print axioms entry161
end Snake9.Regrowth.Bank112
