import E112179Data
import DfsBankData
import CubeLocal
import E112179Complete
namespace Snake9.Regrowth.Bank112
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem prefix_match179 : ∀ i : Fin 112, E112179.pre[i.val]! = (Dfs.oriented 179)[i.val]! := by decide
theorem entry179 (p : Snake 192) (hp : Dfs.StartsWith p (Dfs.oriented 179) 112) : False := by
  have hp' : Dfs.StartsWith p E112179.pre 112 := by
    intro i hi hpLen
    rw [prefix_match179 ⟨i,hi⟩]
    exact hp i hi hpLen
  exact E112179.no192 p hp'
#print axioms entry179
end Snake9.Regrowth.Bank112
