import E112027Data
import DfsBankData
import CubeLocal
import E112027Complete
namespace Snake9.Regrowth.Bank112
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem prefix_match27 : ∀ i : Fin 112, E112027.pre[i.val]! = (Dfs.oriented 27)[i.val]! := by decide
theorem entry27 (p : Snake 192) (hp : Dfs.StartsWith p (Dfs.oriented 27) 112) : False := by
  have hp' : Dfs.StartsWith p E112027.pre 112 := by
    intro i hi hpLen
    rw [prefix_match27 ⟨i,hi⟩]
    exact hp i hi hpLen
  exact E112027.no192 p hp'
#print axioms entry27
end Snake9.Regrowth.Bank112
