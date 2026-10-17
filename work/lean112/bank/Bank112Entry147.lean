import E112147Data
import DfsBankData
import CubeLocal
import E112147Complete
namespace Snake9.Regrowth.Bank112
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem prefix_match147 : ∀ i : Fin 112, E112147.pre[i.val]! = (Dfs.oriented 147)[i.val]! := by decide
theorem entry147 (p : Snake 192) (hp : Dfs.StartsWith p (Dfs.oriented 147) 112) : False := by
  have hp' : Dfs.StartsWith p E112147.pre 112 := by
    intro i hi hpLen
    rw [prefix_match147 ⟨i,hi⟩]
    exact hp i hi hpLen
  exact E112147.no192 p hp'
#print axioms entry147
end Snake9.Regrowth.Bank112
