import E112182Data
import DfsBankData
import CubeLocal
import E112182Complete
namespace Snake9.Regrowth.Bank112
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem prefix_match182 : ∀ i : Fin 112, E112182.pre[i.val]! = (Dfs.oriented 182)[i.val]! := by decide
theorem entry182 (p : Snake 192) (hp : Dfs.StartsWith p (Dfs.oriented 182) 112) : False := by
  have hp' : Dfs.StartsWith p E112182.pre 112 := by
    intro i hi hpLen
    rw [prefix_match182 ⟨i,hi⟩]
    exact hp i hi hpLen
  exact E112182.no192 p hp'
#print axioms entry182
end Snake9.Regrowth.Bank112
