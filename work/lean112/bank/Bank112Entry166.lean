import E112166Data
import DfsBankData
import CubeLocal
import E112166Complete
namespace Snake9.Regrowth.Bank112
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem prefix_match166 : ∀ i : Fin 112, E112166.pre[i.val]! = (Dfs.oriented 166)[i.val]! := by decide
theorem entry166 (p : Snake 192) (hp : Dfs.StartsWith p (Dfs.oriented 166) 112) : False := by
  have hp' : Dfs.StartsWith p E112166.pre 112 := by
    intro i hi hpLen
    rw [prefix_match166 ⟨i,hi⟩]
    exact hp i hi hpLen
  exact E112166.no192 p hp'
#print axioms entry166
end Snake9.Regrowth.Bank112
