import E112052Data
import DfsBankData
import CubeLocal
import E112052Complete
namespace Snake9.Regrowth.Bank112
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem prefix_match52 : ∀ i : Fin 112, E112052.pre[i.val]! = (Dfs.oriented 52)[i.val]! := by decide
theorem entry52 (p : Snake 192) (hp : Dfs.StartsWith p (Dfs.oriented 52) 112) : False := by
  have hp' : Dfs.StartsWith p E112052.pre 112 := by
    intro i hi hpLen
    rw [prefix_match52 ⟨i,hi⟩]
    exact hp i hi hpLen
  exact E112052.no192 p hp'
#print axioms entry52
end Snake9.Regrowth.Bank112
