import First112Data
import DfsBankData
import CubeLocal
import First112Reuse
namespace Snake9.Regrowth.Bank112
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem prefix_match0 : ∀ i : Fin 112, First112.pre[i.val]! = (Dfs.oriented 0)[i.val]! := by decide
theorem entry0 (p : Snake 192) (hp : Dfs.StartsWith p (Dfs.oriented 0) 112) : False := by
  have hp' : Dfs.StartsWith p First112.pre 112 := by
    intro i hi hpLen
    rw [prefix_match0 ⟨i,hi⟩]
    exact hp i hi hpLen
  exact First112.no192 p hp'
#print axioms entry0
end Snake9.Regrowth.Bank112
