"""State each result for arbitrary distinct coordinate labels."""
from pathlib import Path
import json
HERE=Path(__file__).resolve().parents[1]
cases=json.loads((HERE/'data/cases.json').read_text())
s='\n'.join(f'import CycleExclusion{r["number"]}' for r in cases)+'''
import LocalWindowDirBridge
import Mathlib.Tactic
namespace Snake9.LocalWindow.SingletonPatterns
set_option maxRecDepth 100000
set_option maxHeartbeats 0
'''
for r in cases:
    n=r['number'];ds=r['dirs'];L=len(ds);j=r['position'];named=','.join('abcde'[d] for d in ds)
    premises=f''' {{m : Nat}} (p : Snake m) (r a b c d e : Nat)
    (hn : [a,b,c,d,e].Nodup) (h9 : ∀ x ∈ [a,b,c,d,e], x<9)
    (hr : r+{L} ≤ m)
    (hd : ∀ j, j<{L} → dir p (r+j) = ([{named}] : List Nat).getD j 0)'''
    s+=f'''
theorem exclusion{n}'''+premises+f'''
    (hsmall : coreAlpha p (r+{j}) ≤ 1) : False := by
  have hs := mkPerm_spec hn h9 (by simp)
  apply CycleWindow{n}.excluded_in_snake p (mkPerm [a,b,c,d,e]) r hr
  · intro j hj
    have hjL : j<{L} := by simpa [CycleWindow{n}.directions] using hj
    rw [hd j hjL]
    interval_cases j
'''+''.join(f'    · exact hs {d} (by simp)\n' for d in ds)+f'''
  · intro i hi
    have hiN : i<{L-1} := by simpa [CycleWindow{n}.bounds] using hi
    have hu := coreAlpha_le_21 p (k := r+i+1) (by omega) (by omega)
    interval_cases i <;> simp only [CycleWindow{n}.bounds, List.getD_cons_zero,
      List.getD_cons_succ, Prod.fst, Prod.snd, Nat.zero_le, true_and] <;>
      simp_all only [Nat.add_zero]

theorem lower{n}'''+premises+f''' : 2 ≤ coreAlpha p (r+{j}) := by
  by_contra h
  exact exclusion{n} p r a b c d e hn h9 hr hd (by omega)
#print axioms exclusion{n}
#print axioms lower{n}
'''
s+='end Snake9.LocalWindow.SingletonPatterns\n'
(HERE/'lean/SingletonPatterns.lean').write_text(s,encoding='utf-8')
