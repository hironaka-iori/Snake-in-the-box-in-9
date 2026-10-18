import E112090Data
import DfsBankData
import CubeLocal
import E112090Complete
namespace Snake9.Regrowth.Bank112
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem prefix_match90 : ∀ i : Fin 112, E112090.pre[i.val]! = (Dfs.oriented 90)[i.val]! := by decide
theorem entry90 (p : Snake 192) (hp : Dfs.StartsWith p (Dfs.oriented 90) 112) : False := by
  have hp' : Dfs.StartsWith p E112090.pre 112 := by
    intro i hi hpLen
    rw [prefix_match90 ⟨i,hi⟩]
    exact hp i hi hpLen
  exact E112090.no192 p hp'
#print axioms entry90
end Snake9.Regrowth.Bank112
