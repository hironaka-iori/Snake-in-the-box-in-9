import JointCountTags

namespace Snake9.LocalWindow.JointTags
open Tags

/-- The input list preserves multiplicities when a corner belongs to several centres. -/
theorem multi_centre_count {S E : Nat → Bool} {M : MT}
    (lits : List Nat) (centres : List Centre)
    (hn : lits.all (negP M) = true)
    (hm : lits.map (vl M) = centres.flatMap corners) :
    lits.countP (lv (base S E M)) =
      (centres.map fun c => absentCorners S c.v c.d₁ c.d₂).sum := by
  have h : lits.countP (lv (base S E M)) =
      (lits.map (vl M)).countP (fun v => !S v) := by
    rw [List.countP_map]
    apply List.countP_congr
    intro x hx
    simp [base_negP (List.all_eq_true.1 hn x hx)]
  rw [h,hm]
  clear hm hn h
  induction centres with
  | nil => rfl
  | cons c cs ih =>
    simp only [List.flatMap_cons, List.countP_append, countP_corners_abs,
      List.map_cons, List.sum_cons, ih]

#print axioms multi_centre_count
end Snake9.LocalWindow.JointTags
