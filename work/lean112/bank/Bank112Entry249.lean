import E112249Data
import DfsBankData
import CubeLocal
import E112249Complete
namespace Snake9.Regrowth.Bank112
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem prefix_match249 : ∀ i : Fin 112, E112249.pre[i.val]! = (Dfs.oriented 249)[i.val]! := by decide
theorem entry249 (p : Snake 192) (hp : Dfs.StartsWith p (Dfs.oriented 249) 112) : False := by
  have hp' : Dfs.StartsWith p E112249.pre 112 := by
    intro i hi hpLen
    rw [prefix_match249 ⟨i,hi⟩]
    exact hp i hi hpLen
  exact E112249.no192 p hp'
#print axioms entry249
end Snake9.Regrowth.Bank112
