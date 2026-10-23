import CycleExclusion3
import LocalWindowDirBridge
import Mathlib.Tactic

namespace Snake9.LocalWindow.CycleWindow3

def counts : List Nat := [3,5,4,4,5,3,3]

/-- The selected seven-count phase cannot occur under any distinct coordinate labels. -/
theorem pattern_excluded {m : Nat} (p : Snake m) (r a b c d e : Nat)
    (hn : [a,b,c,d,e].Nodup) (h9 : ∀ x ∈ [a,b,c,d,e], x < 9)
    (hr : r+8 ≤ m)
    (hd : ∀ j, j < 8 → dir p (r+j) = ([a,b,c,d,a,e,c,d] : List Nat).getD j 0)
    (ha : ∀ i, i < 7 → coreAlpha p (r+i+1) = counts.getD i 0) : False := by
  have hs := mkPerm_spec hn h9 (by simp)
  apply excluded_in_snake p (mkPerm [a,b,c,d,e]) r hr
  · intro j hj
    have hj8 : j < 8 := by simpa [directions] using hj
    rw [hd j hj8]
    interval_cases j
    · exact hs 0 (by simp)
    · exact hs 1 (by simp)
    · exact hs 2 (by simp)
    · exact hs 3 (by simp)
    · exact hs 0 (by simp)
    · exact hs 4 (by simp)
    · exact hs 2 (by simp)
    · exact hs 3 (by simp)
  · intro i hi
    have hi7 : i < 7 := by simpa [bounds] using hi
    rw [ha i hi7]
    interval_cases i <;> decide +kernel

#print axioms pattern_excluded
end Snake9.LocalWindow.CycleWindow3
