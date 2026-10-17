import E112171Data
import DfsBankData
import CubeLocal
import E112171Complete
namespace Snake9.Regrowth.Bank112
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem prefix_match171 : ∀ i : Fin 112, E112171.pre[i.val]! = (Dfs.oriented 171)[i.val]! := by decide
theorem entry171 (p : Snake 192) (hp : Dfs.StartsWith p (Dfs.oriented 171) 112) : False := by
  have hp' : Dfs.StartsWith p E112171.pre 112 := by
    intro i hi hpLen
    rw [prefix_match171 ⟨i,hi⟩]
    exact hp i hi hpLen
  exact E112171.no192 p hp'
#print axioms entry171
end Snake9.Regrowth.Bank112
