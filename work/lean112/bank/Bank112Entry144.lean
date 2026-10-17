import E112144Data
import DfsBankData
import CubeLocal
import E112144Complete
namespace Snake9.Regrowth.Bank112
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem prefix_match144 : ∀ i : Fin 112, E112144.pre[i.val]! = (Dfs.oriented 144)[i.val]! := by decide
theorem entry144 (p : Snake 192) (hp : Dfs.StartsWith p (Dfs.oriented 144) 112) : False := by
  have hp' : Dfs.StartsWith p E112144.pre 112 := by
    intro i hi hpLen
    rw [prefix_match144 ⟨i,hi⟩]
    exact hp i hi hpLen
  exact E112144.no192 p hp'
#print axioms entry144
end Snake9.Regrowth.Bank112
