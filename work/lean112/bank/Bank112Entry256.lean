import E112256Data
import DfsBankData
import CubeLocal
import E112256Complete
namespace Snake9.Regrowth.Bank112
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem prefix_match256 : ∀ i : Fin 112, E112256.pre[i.val]! = (Dfs.oriented 256)[i.val]! := by decide
theorem entry256 (p : Snake 192) (hp : Dfs.StartsWith p (Dfs.oriented 256) 112) : False := by
  have hp' : Dfs.StartsWith p E112256.pre 112 := by
    intro i hi hpLen
    rw [prefix_match256 ⟨i,hi⟩]
    exact hp i hi hpLen
  exact E112256.no192 p hp'
#print axioms entry256
end Snake9.Regrowth.Bank112
