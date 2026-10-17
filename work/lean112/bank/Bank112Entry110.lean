import E112110Data
import DfsBankData
import CubeLocal
import E112110Complete
namespace Snake9.Regrowth.Bank112
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem prefix_match110 : ∀ i : Fin 112, E112110.pre[i.val]! = (Dfs.oriented 110)[i.val]! := by decide
theorem entry110 (p : Snake 192) (hp : Dfs.StartsWith p (Dfs.oriented 110) 112) : False := by
  have hp' : Dfs.StartsWith p E112110.pre 112 := by
    intro i hi hpLen
    rw [prefix_match110 ⟨i,hi⟩]
    exact hp i hi hpLen
  exact E112110.no192 p hp'
#print axioms entry110
end Snake9.Regrowth.Bank112
