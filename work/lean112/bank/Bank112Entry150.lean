import E112150Data
import DfsBankData
import CubeLocal
import E112150Complete
namespace Snake9.Regrowth.Bank112
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem prefix_match150 : ∀ i : Fin 112, E112150.pre[i.val]! = (Dfs.oriented 150)[i.val]! := by decide
theorem entry150 (p : Snake 192) (hp : Dfs.StartsWith p (Dfs.oriented 150) 112) : False := by
  have hp' : Dfs.StartsWith p E112150.pre 112 := by
    intro i hi hpLen
    rw [prefix_match150 ⟨i,hi⟩]
    exact hp i hi hpLen
  exact E112150.no192 p hp'
#print axioms entry150
end Snake9.Regrowth.Bank112
