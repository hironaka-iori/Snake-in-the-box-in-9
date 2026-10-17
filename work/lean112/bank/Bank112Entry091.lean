import E112091Data
import DfsBankData
import CubeLocal
import E112091Complete
namespace Snake9.Regrowth.Bank112
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem prefix_match91 : ∀ i : Fin 112, E112091.pre[i.val]! = (Dfs.oriented 91)[i.val]! := by decide
theorem entry91 (p : Snake 192) (hp : Dfs.StartsWith p (Dfs.oriented 91) 112) : False := by
  have hp' : Dfs.StartsWith p E112091.pre 112 := by
    intro i hi hpLen
    rw [prefix_match91 ⟨i,hi⟩]
    exact hp i hi hpLen
  exact E112091.no192 p hp'
#print axioms entry91
end Snake9.Regrowth.Bank112
