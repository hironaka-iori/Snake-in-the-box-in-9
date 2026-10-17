import E112205Data
import DfsBankData
import CubeLocal
import E112205Complete
namespace Snake9.Regrowth.Bank112
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem prefix_match205 : ∀ i : Fin 112, E112205.pre[i.val]! = (Dfs.oriented 205)[i.val]! := by decide
theorem entry205 (p : Snake 192) (hp : Dfs.StartsWith p (Dfs.oriented 205) 112) : False := by
  have hp' : Dfs.StartsWith p E112205.pre 112 := by
    intro i hi hpLen
    rw [prefix_match205 ⟨i,hi⟩]
    exact hp i hi hpLen
  exact E112205.no192 p hp'
#print axioms entry205
end Snake9.Regrowth.Bank112
