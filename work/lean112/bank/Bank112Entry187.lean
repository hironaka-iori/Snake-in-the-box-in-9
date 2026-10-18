import E112187Data
import DfsBankData
import CubeLocal
import E112187Complete
namespace Snake9.Regrowth.Bank112
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem prefix_match187 : ∀ i : Fin 112, E112187.pre[i.val]! = (Dfs.oriented 187)[i.val]! := by decide
theorem entry187 (p : Snake 192) (hp : Dfs.StartsWith p (Dfs.oriented 187) 112) : False := by
  have hp' : Dfs.StartsWith p E112187.pre 112 := by
    intro i hi hpLen
    rw [prefix_match187 ⟨i,hi⟩]
    exact hp i hi hpLen
  exact E112187.no192 p hp'
#print axioms entry187
end Snake9.Regrowth.Bank112
