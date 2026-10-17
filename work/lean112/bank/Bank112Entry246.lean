import E112246Data
import DfsBankData
import CubeLocal
import E112246Complete
namespace Snake9.Regrowth.Bank112
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem prefix_match246 : ∀ i : Fin 112, E112246.pre[i.val]! = (Dfs.oriented 246)[i.val]! := by decide
theorem entry246 (p : Snake 192) (hp : Dfs.StartsWith p (Dfs.oriented 246) 112) : False := by
  have hp' : Dfs.StartsWith p E112246.pre 112 := by
    intro i hi hpLen
    rw [prefix_match246 ⟨i,hi⟩]
    exact hp i hi hpLen
  exact E112246.no192 p hp'
#print axioms entry246
end Snake9.Regrowth.Bank112
