import E112158Data
import DfsBankData
import CubeLocal
import E112158Complete
namespace Snake9.Regrowth.Bank112
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem prefix_match158 : ∀ i : Fin 112, E112158.pre[i.val]! = (Dfs.oriented 158)[i.val]! := by decide
theorem entry158 (p : Snake 192) (hp : Dfs.StartsWith p (Dfs.oriented 158) 112) : False := by
  have hp' : Dfs.StartsWith p E112158.pre 112 := by
    intro i hi hpLen
    rw [prefix_match158 ⟨i,hi⟩]
    exact hp i hi hpLen
  exact E112158.no192 p hp'
#print axioms entry158
end Snake9.Regrowth.Bank112
