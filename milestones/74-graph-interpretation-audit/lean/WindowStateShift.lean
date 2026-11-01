import CanonicalShareAdapter

/-! Exact direction-window identities for the current nine-transition graph.
These identify adjacent state shapes; no finite graph membership is assumed. -/
namespace Snake9.GraphInterpretation74
open Snake9.LocalWindow Snake9.WindowAutomaton Snake9.DirectionWindow
open Snake9.CountFreeAdapter73

theorem dsOf_slice {m : Nat} (p : Snake m) (r n s len : Nat)
    (hr : r+n ≤ m) (hs : s+len ≤ n) :
    ((dsOf p r n).drop s).take len = dsOf p (r+s) len := by
  rw [← blockList_eq_dsOf p r n hr, drop_take_blockList p r s len n hs,
    blockList_eq_dsOf p (r+s) len (by omega)]

theorem canonical_nine_source {m : Nat} (p : Snake m) (r : Nat)
    (hr : r+9 ≤ m) :
    canon ((canon (dsOf p r 9)).take 8) = canon (dsOf p r 8) := by
  rw [canon_canon_take]
  have h := dsOf_slice p r 9 0 8 hr (by omega)
  simpa using congrArg canon h

theorem canonical_nine_target {m : Nat} (p : Snake m) (r : Nat)
    (hr : r+9 ≤ m) :
    canon ((canon (dsOf p r 9)).drop 1) = canon (dsOf p (r+1) 8) := by
  rw [canon_canon_drop]
  have h := dsOf_slice p r 9 1 8 hr (by omega)
  have hl : ((dsOf p r 9).drop 1).length = 8 := by simp [length_dsOf]
  rw [List.take_of_length_le (by omega : ((dsOf p r 9).drop 1).length ≤ 8)] at h
  exact congrArg canon h

/-- The suffix used by count-free share dispatch starts at `r+3`, so its
five internal centres are precisely positions `r+4` through `r+8`. -/
theorem canonical_nine_share_suffix {m : Nat} (p : Snake m) (r : Nat)
    (hr : r+9 ≤ m) :
    canon ((canon (dsOf p r 9)).drop 3) = canon (dsOf p (r+3) 6) := by
  rw [canon_canon_drop]
  have h := dsOf_slice p r 9 3 6 hr (by omega)
  have hl : ((dsOf p r 9).drop 3).length = 6 := by simp [length_dsOf]
  rw [List.take_of_length_le (by omega : ((dsOf p r 9).drop 3).length ≤ 6)] at h
  exact congrArg canon h

#print axioms dsOf_slice
#print axioms canonical_nine_source
#print axioms canonical_nine_target
#print axioms canonical_nine_share_suffix
end Snake9.GraphInterpretation74
