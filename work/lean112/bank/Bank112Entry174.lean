import E112174Data
import DfsBankData
import CubeLocal
import E112174Complete
namespace Snake9.Regrowth.Bank112
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem prefix_match174 : ∀ i : Fin 112, E112174.pre[i.val]! = (Dfs.oriented 174)[i.val]! := by decide
theorem entry174 (p : Snake 192) (hp : Dfs.StartsWith p (Dfs.oriented 174) 112) : False := by
  have hp' : Dfs.StartsWith p E112174.pre 112 := by
    intro i hi hpLen
    rw [prefix_match174 ⟨i,hi⟩]
    exact hp i hi hpLen
  exact E112174.no192 p hp'
#print axioms entry174
end Snake9.Regrowth.Bank112
