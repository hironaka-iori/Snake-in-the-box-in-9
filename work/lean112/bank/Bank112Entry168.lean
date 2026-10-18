import E112168Data
import DfsBankData
import CubeLocal
import E112168Complete
namespace Snake9.Regrowth.Bank112
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem prefix_match168 : ∀ i : Fin 112, E112168.pre[i.val]! = (Dfs.oriented 168)[i.val]! := by decide
theorem entry168 (p : Snake 192) (hp : Dfs.StartsWith p (Dfs.oriented 168) 112) : False := by
  have hp' : Dfs.StartsWith p E112168.pre 112 := by
    intro i hi hpLen
    rw [prefix_match168 ⟨i,hi⟩]
    exact hp i hi hpLen
  exact E112168.no192 p hp'
#print axioms entry168
end Snake9.Regrowth.Bank112
