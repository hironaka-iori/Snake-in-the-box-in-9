import E112242Data
import DfsBankData
import CubeLocal
import E112242Complete
namespace Snake9.Regrowth.Bank112
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem prefix_match242 : ∀ i : Fin 112, E112242.pre[i.val]! = (Dfs.oriented 242)[i.val]! := by decide
theorem entry242 (p : Snake 192) (hp : Dfs.StartsWith p (Dfs.oriented 242) 112) : False := by
  have hp' : Dfs.StartsWith p E112242.pre 112 := by
    intro i hi hpLen
    rw [prefix_match242 ⟨i,hi⟩]
    exact hp i hi hpLen
  exact E112242.no192 p hp'
#print axioms entry242
end Snake9.Regrowth.Bank112
