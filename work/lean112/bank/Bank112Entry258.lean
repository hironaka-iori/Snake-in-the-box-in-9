import E112258Data
import DfsBankData
import CubeLocal
import E112258Complete
namespace Snake9.Regrowth.Bank112
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem prefix_match258 : ∀ i : Fin 112, E112258.pre[i.val]! = (Dfs.oriented 258)[i.val]! := by decide
theorem entry258 (p : Snake 192) (hp : Dfs.StartsWith p (Dfs.oriented 258) 112) : False := by
  have hp' : Dfs.StartsWith p E112258.pre 112 := by
    intro i hi hpLen
    rw [prefix_match258 ⟨i,hi⟩]
    exact hp i hi hpLen
  exact E112258.no192 p hp'
#print axioms entry258
end Snake9.Regrowth.Bank112
