import E112159Data
import DfsBankData
import CubeLocal
import E112159Complete
namespace Snake9.Regrowth.Bank112
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem prefix_match159 : ∀ i : Fin 112, E112159.pre[i.val]! = (Dfs.oriented 159)[i.val]! := by decide
theorem entry159 (p : Snake 192) (hp : Dfs.StartsWith p (Dfs.oriented 159) 112) : False := by
  have hp' : Dfs.StartsWith p E112159.pre 112 := by
    intro i hi hpLen
    rw [prefix_match159 ⟨i,hi⟩]
    exact hp i hi hpLen
  exact E112159.no192 p hp'
#print axioms entry159
end Snake9.Regrowth.Bank112
