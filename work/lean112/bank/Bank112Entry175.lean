import E112175Data
import DfsBankData
import CubeLocal
import E112175Complete
namespace Snake9.Regrowth.Bank112
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem prefix_match175 : ∀ i : Fin 112, E112175.pre[i.val]! = (Dfs.oriented 175)[i.val]! := by decide
theorem entry175 (p : Snake 192) (hp : Dfs.StartsWith p (Dfs.oriented 175) 112) : False := by
  have hp' : Dfs.StartsWith p E112175.pre 112 := by
    intro i hi hpLen
    rw [prefix_match175 ⟨i,hi⟩]
    exact hp i hi hpLen
  exact E112175.no192 p hp'
#print axioms entry175
end Snake9.Regrowth.Bank112
