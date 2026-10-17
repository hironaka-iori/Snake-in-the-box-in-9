import E112170Data
import DfsBankData
import CubeLocal
import E112170Complete
namespace Snake9.Regrowth.Bank112
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem prefix_match170 : ∀ i : Fin 112, E112170.pre[i.val]! = (Dfs.oriented 170)[i.val]! := by decide
theorem entry170 (p : Snake 192) (hp : Dfs.StartsWith p (Dfs.oriented 170) 112) : False := by
  have hp' : Dfs.StartsWith p E112170.pre 112 := by
    intro i hi hpLen
    rw [prefix_match170 ⟨i,hi⟩]
    exact hp i hi hpLen
  exact E112170.no192 p hp'
#print axioms entry170
end Snake9.Regrowth.Bank112
