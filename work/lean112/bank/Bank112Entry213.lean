import E112213Data
import DfsBankData
import CubeLocal
import E112213Complete
namespace Snake9.Regrowth.Bank112
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem prefix_match213 : ∀ i : Fin 112, E112213.pre[i.val]! = (Dfs.oriented 213)[i.val]! := by decide
theorem entry213 (p : Snake 192) (hp : Dfs.StartsWith p (Dfs.oriented 213) 112) : False := by
  have hp' : Dfs.StartsWith p E112213.pre 112 := by
    intro i hi hpLen
    rw [prefix_match213 ⟨i,hi⟩]
    exact hp i hi hpLen
  exact E112213.no192 p hp'
#print axioms entry213
end Snake9.Regrowth.Bank112
