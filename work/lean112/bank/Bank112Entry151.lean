import E112151Data
import DfsBankData
import CubeLocal
import E112151Complete
namespace Snake9.Regrowth.Bank112
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem prefix_match151 : ∀ i : Fin 112, E112151.pre[i.val]! = (Dfs.oriented 151)[i.val]! := by decide
theorem entry151 (p : Snake 192) (hp : Dfs.StartsWith p (Dfs.oriented 151) 112) : False := by
  have hp' : Dfs.StartsWith p E112151.pre 112 := by
    intro i hi hpLen
    rw [prefix_match151 ⟨i,hi⟩]
    exact hp i hi hpLen
  exact E112151.no192 p hp'
#print axioms entry151
end Snake9.Regrowth.Bank112
