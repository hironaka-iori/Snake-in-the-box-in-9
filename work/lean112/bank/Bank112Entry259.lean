import E112259Data
import DfsBankData
import CubeLocal
import E112259Complete
namespace Snake9.Regrowth.Bank112
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem prefix_match259 : ∀ i : Fin 112, E112259.pre[i.val]! = (Dfs.oriented 259)[i.val]! := by decide
theorem entry259 (p : Snake 192) (hp : Dfs.StartsWith p (Dfs.oriented 259) 112) : False := by
  have hp' : Dfs.StartsWith p E112259.pre 112 := by
    intro i hi hpLen
    rw [prefix_match259 ⟨i,hi⟩]
    exact hp i hi hpLen
  exact E112259.no192 p hp'
#print axioms entry259
end Snake9.Regrowth.Bank112
