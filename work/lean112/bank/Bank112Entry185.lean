import E112185Data
import DfsBankData
import CubeLocal
import E112185Complete
namespace Snake9.Regrowth.Bank112
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem prefix_match185 : ∀ i : Fin 112, E112185.pre[i.val]! = (Dfs.oriented 185)[i.val]! := by decide
theorem entry185 (p : Snake 192) (hp : Dfs.StartsWith p (Dfs.oriented 185) 112) : False := by
  have hp' : Dfs.StartsWith p E112185.pre 112 := by
    intro i hi hpLen
    rw [prefix_match185 ⟨i,hi⟩]
    exact hp i hi hpLen
  exact E112185.no192 p hp'
#print axioms entry185
end Snake9.Regrowth.Bank112
