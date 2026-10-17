import E112097Data
import DfsBankData
import CubeLocal
import E112097Complete
namespace Snake9.Regrowth.Bank112
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem prefix_match97 : ∀ i : Fin 112, E112097.pre[i.val]! = (Dfs.oriented 97)[i.val]! := by decide
theorem entry97 (p : Snake 192) (hp : Dfs.StartsWith p (Dfs.oriented 97) 112) : False := by
  have hp' : Dfs.StartsWith p E112097.pre 112 := by
    intro i hi hpLen
    rw [prefix_match97 ⟨i,hi⟩]
    exact hp i hi hpLen
  exact E112097.no192 p hp'
#print axioms entry97
end Snake9.Regrowth.Bank112
