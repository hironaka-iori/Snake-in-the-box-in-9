import E112154Data
import DfsBankData
import CubeLocal
import E112154Complete
namespace Snake9.Regrowth.Bank112
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem prefix_match154 : ∀ i : Fin 112, E112154.pre[i.val]! = (Dfs.oriented 154)[i.val]! := by decide
theorem entry154 (p : Snake 192) (hp : Dfs.StartsWith p (Dfs.oriented 154) 112) : False := by
  have hp' : Dfs.StartsWith p E112154.pre 112 := by
    intro i hi hpLen
    rw [prefix_match154 ⟨i,hi⟩]
    exact hp i hi hpLen
  exact E112154.no192 p hp'
#print axioms entry154
end Snake9.Regrowth.Bank112
