import E112152Data
import DfsBankData
import CubeLocal
import E112152Complete
namespace Snake9.Regrowth.Bank112
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem prefix_match152 : ∀ i : Fin 112, E112152.pre[i.val]! = (Dfs.oriented 152)[i.val]! := by decide
theorem entry152 (p : Snake 192) (hp : Dfs.StartsWith p (Dfs.oriented 152) 112) : False := by
  have hp' : Dfs.StartsWith p E112152.pre 112 := by
    intro i hi hpLen
    rw [prefix_match152 ⟨i,hi⟩]
    exact hp i hi hpLen
  exact E112152.no192 p hp'
#print axioms entry152
end Snake9.Regrowth.Bank112
