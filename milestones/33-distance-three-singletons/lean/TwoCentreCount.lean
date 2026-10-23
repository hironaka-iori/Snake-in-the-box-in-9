import JointCountTags
namespace Snake9.LocalWindow.JointTags
open Tags
variable {M : MT} {S E : Nat → Bool}
/-- Concatenating opposite-corner lists adds singleton counts, including
the multiplicities of corner vertices shared between centres. -/
theorem two_centre_count (lits : List Nat) (a b : Centre)
    (hn : lits.all (negP M) = true)
    (hm : lits.map (vl M) = corners a ++ corners b) :
    lits.countP (lv (base S E M)) =
      absentCorners S a.v a.d₁ a.d₂ + absentCorners S b.v b.d₁ b.d₂ := by
  have h : lits.countP (lv (base S E M)) = (lits.map (vl M)).countP (fun v => !S v) := by
    rw [List.countP_map]
    apply List.countP_congr
    intro x hx
    simp [base_negP (List.all_eq_true.1 hn x hx)]
  rw [h, hm]
  simp only [List.countP_append, countP_corners_abs]


#print axioms two_centre_count
end Snake9.LocalWindow.JointTags
