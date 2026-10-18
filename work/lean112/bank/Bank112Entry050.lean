import E112050Data
import DfsBankData
import CubeLocal
import E112050Complete
namespace Snake9.Regrowth.Bank112
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem prefix_match50 : ∀ i : Fin 112, E112050.pre[i.val]! = (Dfs.oriented 50)[i.val]! := by decide
theorem entry50 (p : Snake 192) (hp : Dfs.StartsWith p (Dfs.oriented 50) 112) : False := by
  have hp' : Dfs.StartsWith p E112050.pre 112 := by
    intro i hi hpLen
    rw [prefix_match50 ⟨i,hi⟩]
    exact hp i hi hpLen
  exact E112050.no192 p hp'
#print axioms entry50
end Snake9.Regrowth.Bank112
