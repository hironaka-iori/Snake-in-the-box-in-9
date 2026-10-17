import E112034Data
import DfsBankData
import CubeLocal
import E112034Complete
namespace Snake9.Regrowth.Bank112
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem prefix_match34 : ∀ i : Fin 112, E112034.pre[i.val]! = (Dfs.oriented 34)[i.val]! := by decide
theorem entry34 (p : Snake 192) (hp : Dfs.StartsWith p (Dfs.oriented 34) 112) : False := by
  have hp' : Dfs.StartsWith p E112034.pre 112 := by
    intro i hi hpLen
    rw [prefix_match34 ⟨i,hi⟩]
    exact hp i hi hpLen
  exact E112034.no192 p hp'
#print axioms entry34
end Snake9.Regrowth.Bank112
