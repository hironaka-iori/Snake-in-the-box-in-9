import E112186Data
import DfsBankData
import CubeLocal
import E112186Complete
namespace Snake9.Regrowth.Bank112
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem prefix_match186 : ∀ i : Fin 112, E112186.pre[i.val]! = (Dfs.oriented 186)[i.val]! := by decide
theorem entry186 (p : Snake 192) (hp : Dfs.StartsWith p (Dfs.oriented 186) 112) : False := by
  have hp' : Dfs.StartsWith p E112186.pre 112 := by
    intro i hi hpLen
    rw [prefix_match186 ⟨i,hi⟩]
    exact hp i hi hpLen
  exact E112186.no192 p hp'
#print axioms entry186
end Snake9.Regrowth.Bank112
