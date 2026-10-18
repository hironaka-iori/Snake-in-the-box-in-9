import E112225Data
import DfsBankData
import CubeLocal
import E112225Complete
namespace Snake9.Regrowth.Bank112
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem prefix_match225 : ∀ i : Fin 112, E112225.pre[i.val]! = (Dfs.oriented 225)[i.val]! := by decide
theorem entry225 (p : Snake 192) (hp : Dfs.StartsWith p (Dfs.oriented 225) 112) : False := by
  have hp' : Dfs.StartsWith p E112225.pre 112 := by
    intro i hi hpLen
    rw [prefix_match225 ⟨i,hi⟩]
    exact hp i hi hpLen
  exact E112225.no192 p hp'
#print axioms entry225
end Snake9.Regrowth.Bank112
