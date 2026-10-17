import E112094Data
import DfsBankData
import CubeLocal
import E112094Complete
namespace Snake9.Regrowth.Bank112
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem prefix_match94 : ∀ i : Fin 112, E112094.pre[i.val]! = (Dfs.oriented 94)[i.val]! := by decide
theorem entry94 (p : Snake 192) (hp : Dfs.StartsWith p (Dfs.oriented 94) 112) : False := by
  have hp' : Dfs.StartsWith p E112094.pre 112 := by
    intro i hi hpLen
    rw [prefix_match94 ⟨i,hi⟩]
    exact hp i hi hpLen
  exact E112094.no192 p hp'
#print axioms entry94
end Snake9.Regrowth.Bank112
