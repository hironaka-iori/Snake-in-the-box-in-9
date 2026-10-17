import E112096Data
import DfsBankData
import CubeLocal
import E112096Complete
namespace Snake9.Regrowth.Bank112
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem prefix_match96 : ∀ i : Fin 112, E112096.pre[i.val]! = (Dfs.oriented 96)[i.val]! := by decide
theorem entry96 (p : Snake 192) (hp : Dfs.StartsWith p (Dfs.oriented 96) 112) : False := by
  have hp' : Dfs.StartsWith p E112096.pre 112 := by
    intro i hi hpLen
    rw [prefix_match96 ⟨i,hi⟩]
    exact hp i hi hpLen
  exact E112096.no192 p hp'
#print axioms entry96
end Snake9.Regrowth.Bank112
