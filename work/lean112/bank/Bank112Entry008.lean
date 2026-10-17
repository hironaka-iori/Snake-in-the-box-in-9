import E112008Data
import DfsBankData
import CubeLocal
import E112008Complete
namespace Snake9.Regrowth.Bank112
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem prefix_match8 : ∀ i : Fin 112, E112008.pre[i.val]! = (Dfs.oriented 8)[i.val]! := by decide
theorem entry8 (p : Snake 192) (hp : Dfs.StartsWith p (Dfs.oriented 8) 112) : False := by
  have hp' : Dfs.StartsWith p E112008.pre 112 := by
    intro i hi hpLen
    rw [prefix_match8 ⟨i,hi⟩]
    exact hp i hi hpLen
  exact E112008.no192 p hp'
#print axioms entry8
end Snake9.Regrowth.Bank112
