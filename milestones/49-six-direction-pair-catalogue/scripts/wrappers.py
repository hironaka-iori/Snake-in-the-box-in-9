"""Generate general labelled statements for all basis exclusions."""
from pathlib import Path
import json
HERE=Path(__file__).resolve().parents[1]
for c in json.loads((HERE/'data/cases.json').read_text()):
 n=c['number'];ds=c['dirs'];L=len(ds);letters='abcdef'[:max(ds)+1];labels=','.join(letters);named=','.join(letters[d] for d in ds);j,k=c['positions'];u,v=c['caps']
 s=f'''import CycleExclusion{n}
import LocalWindowDirBridge
import Mathlib.Tactic
namespace Snake9.LocalWindow.PairBasis{n}
set_option maxHeartbeats 0

theorem exclusion {{m : Nat}} (p : Snake m) (r {' '.join(letters)} : Nat)
    (hn : [{labels}].Nodup) (h9 : ∀ x ∈ [{labels}], x<9)
    (hr : r+{L} ≤ m)
    (hd : ∀ j, j<{L} → dir p (r+j) = ([{named}] : List Nat).getD j 0)
    (hfirst : coreAlpha p (r+{j}) ≤ {u}) (hsecond : coreAlpha p (r+{k}) ≤ {v}) : False := by
  have hs := mkPerm_spec hn h9 (by simp)
  apply CycleWindow{n}.excluded_in_snake p (mkPerm [{labels}]) r hr
  · intro j hj
    have hjL : j<{L} := by simpa [CycleWindow{n}.directions] using hj
    rw [hd j hjL]
    interval_cases j
'''+''.join(f'    · exact hs {d} (by simp)\n' for d in ds)+f'''  · intro i hi
    have hiN : i<{L-1} := by simpa [CycleWindow{n}.bounds] using hi
    have hu := coreAlpha_le_21 p (k := r+i+1) (by omega) (by omega)
    interval_cases i <;> simp only [CycleWindow{n}.bounds, List.getD_cons_zero,
      List.getD_cons_succ, Prod.fst, Prod.snd, Nat.zero_le, true_and] <;>
      simp_all only [Nat.add_zero]
#print axioms exclusion
end Snake9.LocalWindow.PairBasis{n}
'''
 (HERE/f'lean/PairBasis{n}.lean').write_text(s,encoding='utf-8')
