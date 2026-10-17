import E112115Data
import DfsBankData
import CubeLocal
import E112115Complete
namespace Snake9.Regrowth.Bank112
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem prefix_match115 : ∀ i : Fin 112, E112115.pre[i.val]! = (Dfs.oriented 115)[i.val]! := by decide
theorem entry115 (p : Snake 192) (hp : Dfs.StartsWith p (Dfs.oriented 115) 112) : False := by
  have hp' : Dfs.StartsWith p E112115.pre 112 := by
    intro i hi hpLen
    rw [prefix_match115 ⟨i,hi⟩]
    exact hp i hi hpLen
  exact E112115.no192 p hp'
#print axioms entry115
end Snake9.Regrowth.Bank112
