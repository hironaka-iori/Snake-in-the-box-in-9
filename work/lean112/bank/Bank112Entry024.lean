import E112024Data
import DfsBankData
import CubeLocal
import E112024Complete
namespace Snake9.Regrowth.Bank112
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem prefix_match24 : ∀ i : Fin 112, E112024.pre[i.val]! = (Dfs.oriented 24)[i.val]! := by decide
theorem entry24 (p : Snake 192) (hp : Dfs.StartsWith p (Dfs.oriented 24) 112) : False := by
  have hp' : Dfs.StartsWith p E112024.pre 112 := by
    intro i hi hpLen
    rw [prefix_match24 ⟨i,hi⟩]
    exact hp i hi hpLen
  exact E112024.no192 p hp'
#print axioms entry24
end Snake9.Regrowth.Bank112
