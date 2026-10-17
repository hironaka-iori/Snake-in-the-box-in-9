import E112007Data
import DfsBankData
import CubeLocal
import E112007Complete
namespace Snake9.Regrowth.Bank112
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem prefix_match7 : ∀ i : Fin 112, E112007.pre[i.val]! = (Dfs.oriented 7)[i.val]! := by decide
theorem entry7 (p : Snake 192) (hp : Dfs.StartsWith p (Dfs.oriented 7) 112) : False := by
  have hp' : Dfs.StartsWith p E112007.pre 112 := by
    intro i hi hpLen
    rw [prefix_match7 ⟨i,hi⟩]
    exact hp i hi hpLen
  exact E112007.no192 p hp'
#print axioms entry7
end Snake9.Regrowth.Bank112
