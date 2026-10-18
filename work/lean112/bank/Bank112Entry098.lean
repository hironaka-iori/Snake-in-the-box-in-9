import E112098Data
import DfsBankData
import CubeLocal
import E112098Complete
namespace Snake9.Regrowth.Bank112
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem prefix_match98 : ∀ i : Fin 112, E112098.pre[i.val]! = (Dfs.oriented 98)[i.val]! := by decide
theorem entry98 (p : Snake 192) (hp : Dfs.StartsWith p (Dfs.oriented 98) 112) : False := by
  have hp' : Dfs.StartsWith p E112098.pre 112 := by
    intro i hi hpLen
    rw [prefix_match98 ⟨i,hi⟩]
    exact hp i hi hpLen
  exact E112098.no192 p hp'
#print axioms entry98
end Snake9.Regrowth.Bank112
