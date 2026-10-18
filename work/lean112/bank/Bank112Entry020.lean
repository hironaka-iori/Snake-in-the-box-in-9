import E112020Data
import DfsBankData
import CubeLocal
import E112020Complete
namespace Snake9.Regrowth.Bank112
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem prefix_match20 : ∀ i : Fin 112, E112020.pre[i.val]! = (Dfs.oriented 20)[i.val]! := by decide
theorem entry20 (p : Snake 192) (hp : Dfs.StartsWith p (Dfs.oriented 20) 112) : False := by
  have hp' : Dfs.StartsWith p E112020.pre 112 := by
    intro i hi hpLen
    rw [prefix_match20 ⟨i,hi⟩]
    exact hp i hi hpLen
  exact E112020.no192 p hp'
#print axioms entry20
end Snake9.Regrowth.Bank112
