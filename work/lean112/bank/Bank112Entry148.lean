import E112148Data
import DfsBankData
import CubeLocal
import E112148Complete
namespace Snake9.Regrowth.Bank112
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem prefix_match148 : ∀ i : Fin 112, E112148.pre[i.val]! = (Dfs.oriented 148)[i.val]! := by decide
theorem entry148 (p : Snake 192) (hp : Dfs.StartsWith p (Dfs.oriented 148) 112) : False := by
  have hp' : Dfs.StartsWith p E112148.pre 112 := by
    intro i hi hpLen
    rw [prefix_match148 ⟨i,hi⟩]
    exact hp i hi hpLen
  exact E112148.no192 p hp'
#print axioms entry148
end Snake9.Regrowth.Bank112
