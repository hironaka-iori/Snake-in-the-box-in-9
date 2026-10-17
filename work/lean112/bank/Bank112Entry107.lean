import E112107Data
import DfsBankData
import CubeLocal
import E112107Complete
namespace Snake9.Regrowth.Bank112
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem prefix_match107 : ∀ i : Fin 112, E112107.pre[i.val]! = (Dfs.oriented 107)[i.val]! := by decide
theorem entry107 (p : Snake 192) (hp : Dfs.StartsWith p (Dfs.oriented 107) 112) : False := by
  have hp' : Dfs.StartsWith p E112107.pre 112 := by
    intro i hi hpLen
    rw [prefix_match107 ⟨i,hi⟩]
    exact hp i hi hpLen
  exact E112107.no192 p hp'
#print axioms entry107
end Snake9.Regrowth.Bank112
