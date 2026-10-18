import E112145Data
import DfsBankData
import CubeLocal
import E112145Complete
namespace Snake9.Regrowth.Bank112
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem prefix_match145 : ∀ i : Fin 112, E112145.pre[i.val]! = (Dfs.oriented 145)[i.val]! := by decide
theorem entry145 (p : Snake 192) (hp : Dfs.StartsWith p (Dfs.oriented 145) 112) : False := by
  have hp' : Dfs.StartsWith p E112145.pre 112 := by
    intro i hi hpLen
    rw [prefix_match145 ⟨i,hi⟩]
    exact hp i hi hpLen
  exact E112145.no192 p hp'
#print axioms entry145
end Snake9.Regrowth.Bank112
