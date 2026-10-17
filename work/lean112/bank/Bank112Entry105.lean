import E112105Data
import DfsBankData
import CubeLocal
import E112105Complete
namespace Snake9.Regrowth.Bank112
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem prefix_match105 : ∀ i : Fin 112, E112105.pre[i.val]! = (Dfs.oriented 105)[i.val]! := by decide
theorem entry105 (p : Snake 192) (hp : Dfs.StartsWith p (Dfs.oriented 105) 112) : False := by
  have hp' : Dfs.StartsWith p E112105.pre 112 := by
    intro i hi hpLen
    rw [prefix_match105 ⟨i,hi⟩]
    exact hp i hi hpLen
  exact E112105.no192 p hp'
#print axioms entry105
end Snake9.Regrowth.Bank112
