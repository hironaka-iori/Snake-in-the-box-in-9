import E112036Data
import DfsBankData
import CubeLocal
import E112036Complete
namespace Snake9.Regrowth.Bank112
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem prefix_match36 : ∀ i : Fin 112, E112036.pre[i.val]! = (Dfs.oriented 36)[i.val]! := by decide
theorem entry36 (p : Snake 192) (hp : Dfs.StartsWith p (Dfs.oriented 36) 112) : False := by
  have hp' : Dfs.StartsWith p E112036.pre 112 := by
    intro i hi hpLen
    rw [prefix_match36 ⟨i,hi⟩]
    exact hp i hi hpLen
  exact E112036.no192 p hp'
#print axioms entry36
end Snake9.Regrowth.Bank112
