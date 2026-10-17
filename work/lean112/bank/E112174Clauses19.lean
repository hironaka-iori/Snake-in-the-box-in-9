import E112174Semantics
import B112E174Inputs
namespace Snake9.Regrowth.E112174
noncomputable section
local instance blockDec19 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause609 (q : Nat → Bool) : valuationOf q 750 = false ∨ valuationOf q 776 = true := by
  have hs : count776 q = (countLit q [-27, -28, -31, -33, -34, -36]) + (countLit q [-38, -41, -43, -45, -48, -50, -51]) := List.countP_append (p := literal q) (l₁ := [-27, -28, -31, -33, -34, -36]) (l₂ := [-38, -41, -43, -45, -48, -50, -51])
  have hm := merge_left (literal (valuationOf q) (750)) (literal (valuationOf q) (776)) (countLit q [-27, -28, -31, -33, -34, -36]) (countLit q [-38, -41, -43, -45, -48, -50, -51]) (count776 q) 1 (meaning750 q) (meaning776 q) hs
  change valuationOf q 750 = false ∨ valuationOf q 776 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause609 (q : Snake 81) (h : Conditions q) : valuation q 750 = false ∨ valuation q 776 = true := counterClause609 (baseVal q)

theorem counterClause610 (q : Nat → Bool) : valuationOf q 750 = false ∨ valuationOf q 769 = false ∨ valuationOf q 777 = true := by
  have hs : count776 q = (countLit q [-27, -28, -31, -33, -34, -36]) + (countLit q [-38, -41, -43, -45, -48, -50, -51]) := List.countP_append (p := literal q) (l₁ := [-27, -28, -31, -33, -34, -36]) (l₂ := [-38, -41, -43, -45, -48, -50, -51])
  have hm := merge_two (literal (valuationOf q) (750)) (literal (valuationOf q) (769)) (literal (valuationOf q) (777)) (countLit q [-27, -28, -31, -33, -34, -36]) (countLit q [-38, -41, -43, -45, -48, -50, -51]) (count776 q) 1 1 (meaning750 q) (meaning769 q) (meaning777 q) hs
  change valuationOf q 750 = false ∨ valuationOf q 769 = false ∨ valuationOf q 777 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause610 (q : Snake 81) (h : Conditions q) : valuation q 750 = false ∨ valuation q 769 = false ∨ valuation q 777 = true := counterClause610 (baseVal q)

theorem counterClause611 (q : Nat → Bool) : valuationOf q 750 = false ∨ valuationOf q 770 = false ∨ valuationOf q 778 = true := by
  have hs : count776 q = (countLit q [-27, -28, -31, -33, -34, -36]) + (countLit q [-38, -41, -43, -45, -48, -50, -51]) := List.countP_append (p := literal q) (l₁ := [-27, -28, -31, -33, -34, -36]) (l₂ := [-38, -41, -43, -45, -48, -50, -51])
  have hm := merge_two (literal (valuationOf q) (750)) (literal (valuationOf q) (770)) (literal (valuationOf q) (778)) (countLit q [-27, -28, -31, -33, -34, -36]) (countLit q [-38, -41, -43, -45, -48, -50, -51]) (count776 q) 1 2 (meaning750 q) (meaning770 q) (meaning778 q) hs
  change valuationOf q 750 = false ∨ valuationOf q 770 = false ∨ valuationOf q 778 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause611 (q : Snake 81) (h : Conditions q) : valuation q 750 = false ∨ valuation q 770 = false ∨ valuation q 778 = true := counterClause611 (baseVal q)

theorem counterClause612 (q : Nat → Bool) : valuationOf q 750 = false ∨ valuationOf q 771 = false ∨ valuationOf q 779 = true := by
  have hs : count776 q = (countLit q [-27, -28, -31, -33, -34, -36]) + (countLit q [-38, -41, -43, -45, -48, -50, -51]) := List.countP_append (p := literal q) (l₁ := [-27, -28, -31, -33, -34, -36]) (l₂ := [-38, -41, -43, -45, -48, -50, -51])
  have hm := merge_two (literal (valuationOf q) (750)) (literal (valuationOf q) (771)) (literal (valuationOf q) (779)) (countLit q [-27, -28, -31, -33, -34, -36]) (countLit q [-38, -41, -43, -45, -48, -50, -51]) (count776 q) 1 3 (meaning750 q) (meaning771 q) (meaning779 q) hs
  change valuationOf q 750 = false ∨ valuationOf q 771 = false ∨ valuationOf q 779 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause612 (q : Snake 81) (h : Conditions q) : valuation q 750 = false ∨ valuation q 771 = false ∨ valuation q 779 = true := counterClause612 (baseVal q)

theorem counterClause613 (q : Nat → Bool) : valuationOf q 751 = false ∨ valuationOf q 777 = true := by
  have hs : count776 q = (countLit q [-27, -28, -31, -33, -34, -36]) + (countLit q [-38, -41, -43, -45, -48, -50, -51]) := List.countP_append (p := literal q) (l₁ := [-27, -28, -31, -33, -34, -36]) (l₂ := [-38, -41, -43, -45, -48, -50, -51])
  have hm := merge_left (literal (valuationOf q) (751)) (literal (valuationOf q) (777)) (countLit q [-27, -28, -31, -33, -34, -36]) (countLit q [-38, -41, -43, -45, -48, -50, -51]) (count776 q) 2 (meaning751 q) (meaning777 q) hs
  change valuationOf q 751 = false ∨ valuationOf q 777 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause613 (q : Snake 81) (h : Conditions q) : valuation q 751 = false ∨ valuation q 777 = true := counterClause613 (baseVal q)

theorem counterClause614 (q : Nat → Bool) : valuationOf q 751 = false ∨ valuationOf q 769 = false ∨ valuationOf q 778 = true := by
  have hs : count776 q = (countLit q [-27, -28, -31, -33, -34, -36]) + (countLit q [-38, -41, -43, -45, -48, -50, -51]) := List.countP_append (p := literal q) (l₁ := [-27, -28, -31, -33, -34, -36]) (l₂ := [-38, -41, -43, -45, -48, -50, -51])
  have hm := merge_two (literal (valuationOf q) (751)) (literal (valuationOf q) (769)) (literal (valuationOf q) (778)) (countLit q [-27, -28, -31, -33, -34, -36]) (countLit q [-38, -41, -43, -45, -48, -50, -51]) (count776 q) 2 1 (meaning751 q) (meaning769 q) (meaning778 q) hs
  change valuationOf q 751 = false ∨ valuationOf q 769 = false ∨ valuationOf q 778 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause614 (q : Snake 81) (h : Conditions q) : valuation q 751 = false ∨ valuation q 769 = false ∨ valuation q 778 = true := counterClause614 (baseVal q)

theorem counterClause615 (q : Nat → Bool) : valuationOf q 751 = false ∨ valuationOf q 770 = false ∨ valuationOf q 779 = true := by
  have hs : count776 q = (countLit q [-27, -28, -31, -33, -34, -36]) + (countLit q [-38, -41, -43, -45, -48, -50, -51]) := List.countP_append (p := literal q) (l₁ := [-27, -28, -31, -33, -34, -36]) (l₂ := [-38, -41, -43, -45, -48, -50, -51])
  have hm := merge_two (literal (valuationOf q) (751)) (literal (valuationOf q) (770)) (literal (valuationOf q) (779)) (countLit q [-27, -28, -31, -33, -34, -36]) (countLit q [-38, -41, -43, -45, -48, -50, -51]) (count776 q) 2 2 (meaning751 q) (meaning770 q) (meaning779 q) hs
  change valuationOf q 751 = false ∨ valuationOf q 770 = false ∨ valuationOf q 779 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause615 (q : Snake 81) (h : Conditions q) : valuation q 751 = false ∨ valuation q 770 = false ∨ valuation q 779 = true := counterClause615 (baseVal q)

theorem counterClause616 (q : Nat → Bool) : valuationOf q 751 = false ∨ valuationOf q 771 = false ∨ valuationOf q 780 = true := by
  have hs : count776 q = (countLit q [-27, -28, -31, -33, -34, -36]) + (countLit q [-38, -41, -43, -45, -48, -50, -51]) := List.countP_append (p := literal q) (l₁ := [-27, -28, -31, -33, -34, -36]) (l₂ := [-38, -41, -43, -45, -48, -50, -51])
  have hm := merge_two (literal (valuationOf q) (751)) (literal (valuationOf q) (771)) (literal (valuationOf q) (780)) (countLit q [-27, -28, -31, -33, -34, -36]) (countLit q [-38, -41, -43, -45, -48, -50, -51]) (count776 q) 2 3 (meaning751 q) (meaning771 q) (meaning780 q) hs
  change valuationOf q 751 = false ∨ valuationOf q 771 = false ∨ valuationOf q 780 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause616 (q : Snake 81) (h : Conditions q) : valuation q 751 = false ∨ valuation q 771 = false ∨ valuation q 780 = true := counterClause616 (baseVal q)

theorem counterClause617 (q : Nat → Bool) : valuationOf q 752 = false ∨ valuationOf q 778 = true := by
  have hs : count776 q = (countLit q [-27, -28, -31, -33, -34, -36]) + (countLit q [-38, -41, -43, -45, -48, -50, -51]) := List.countP_append (p := literal q) (l₁ := [-27, -28, -31, -33, -34, -36]) (l₂ := [-38, -41, -43, -45, -48, -50, -51])
  have hm := merge_left (literal (valuationOf q) (752)) (literal (valuationOf q) (778)) (countLit q [-27, -28, -31, -33, -34, -36]) (countLit q [-38, -41, -43, -45, -48, -50, -51]) (count776 q) 3 (meaning752 q) (meaning778 q) hs
  change valuationOf q 752 = false ∨ valuationOf q 778 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause617 (q : Snake 81) (h : Conditions q) : valuation q 752 = false ∨ valuation q 778 = true := counterClause617 (baseVal q)

theorem counterClause618 (q : Nat → Bool) : valuationOf q 752 = false ∨ valuationOf q 769 = false ∨ valuationOf q 779 = true := by
  have hs : count776 q = (countLit q [-27, -28, -31, -33, -34, -36]) + (countLit q [-38, -41, -43, -45, -48, -50, -51]) := List.countP_append (p := literal q) (l₁ := [-27, -28, -31, -33, -34, -36]) (l₂ := [-38, -41, -43, -45, -48, -50, -51])
  have hm := merge_two (literal (valuationOf q) (752)) (literal (valuationOf q) (769)) (literal (valuationOf q) (779)) (countLit q [-27, -28, -31, -33, -34, -36]) (countLit q [-38, -41, -43, -45, -48, -50, -51]) (count776 q) 3 1 (meaning752 q) (meaning769 q) (meaning779 q) hs
  change valuationOf q 752 = false ∨ valuationOf q 769 = false ∨ valuationOf q 779 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause618 (q : Snake 81) (h : Conditions q) : valuation q 752 = false ∨ valuation q 769 = false ∨ valuation q 779 = true := counterClause618 (baseVal q)

theorem counterClause619 (q : Nat → Bool) : valuationOf q 752 = false ∨ valuationOf q 770 = false ∨ valuationOf q 780 = true := by
  have hs : count776 q = (countLit q [-27, -28, -31, -33, -34, -36]) + (countLit q [-38, -41, -43, -45, -48, -50, -51]) := List.countP_append (p := literal q) (l₁ := [-27, -28, -31, -33, -34, -36]) (l₂ := [-38, -41, -43, -45, -48, -50, -51])
  have hm := merge_two (literal (valuationOf q) (752)) (literal (valuationOf q) (770)) (literal (valuationOf q) (780)) (countLit q [-27, -28, -31, -33, -34, -36]) (countLit q [-38, -41, -43, -45, -48, -50, -51]) (count776 q) 3 2 (meaning752 q) (meaning770 q) (meaning780 q) hs
  change valuationOf q 752 = false ∨ valuationOf q 770 = false ∨ valuationOf q 780 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause619 (q : Snake 81) (h : Conditions q) : valuation q 752 = false ∨ valuation q 770 = false ∨ valuation q 780 = true := counterClause619 (baseVal q)

theorem counterClause620 (q : Nat → Bool) : valuationOf q 752 = false ∨ valuationOf q 771 = false ∨ valuationOf q 781 = true := by
  have hs : count776 q = (countLit q [-27, -28, -31, -33, -34, -36]) + (countLit q [-38, -41, -43, -45, -48, -50, -51]) := List.countP_append (p := literal q) (l₁ := [-27, -28, -31, -33, -34, -36]) (l₂ := [-38, -41, -43, -45, -48, -50, -51])
  have hm := merge_two (literal (valuationOf q) (752)) (literal (valuationOf q) (771)) (literal (valuationOf q) (781)) (countLit q [-27, -28, -31, -33, -34, -36]) (countLit q [-38, -41, -43, -45, -48, -50, -51]) (count776 q) 3 3 (meaning752 q) (meaning771 q) (meaning781 q) hs
  change valuationOf q 752 = false ∨ valuationOf q 771 = false ∨ valuationOf q 781 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause620 (q : Snake 81) (h : Conditions q) : valuation q 752 = false ∨ valuation q 771 = false ∨ valuation q 781 = true := counterClause620 (baseVal q)

theorem counterClause621 (q : Nat → Bool) : valuationOf q 779 = false ∨ valuationOf q 790 = true := by
  have hs : count787 q = (countLit q [-3, -4, -6, -10, -12, -14, -16, -17, -18, -21, -22, -25]) + (countLit q [-27, -28, -31, -33, -34, -36, -38, -41, -43, -45, -48, -50, -51]) := List.countP_append (p := literal q) (l₁ := [-3, -4, -6, -10, -12, -14, -16, -17, -18, -21, -22, -25]) (l₂ := [-27, -28, -31, -33, -34, -36, -38, -41, -43, -45, -48, -50, -51])
  have hm := merge_right (literal (valuationOf q) (779)) (literal (valuationOf q) (790)) (countLit q [-3, -4, -6, -10, -12, -14, -16, -17, -18, -21, -22, -25]) (countLit q [-27, -28, -31, -33, -34, -36, -38, -41, -43, -45, -48, -50, -51]) (count787 q) 4 (meaning779 q) (meaning790 q) hs
  change valuationOf q 779 = false ∨ valuationOf q 790 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause621 (q : Snake 81) (h : Conditions q) : valuation q 779 = false ∨ valuation q 790 = true := counterClause621 (baseVal q)

theorem counterClause622 (q : Nat → Bool) : valuationOf q 781 = false ∨ valuationOf q 792 = true := by
  have hs : count787 q = (countLit q [-3, -4, -6, -10, -12, -14, -16, -17, -18, -21, -22, -25]) + (countLit q [-27, -28, -31, -33, -34, -36, -38, -41, -43, -45, -48, -50, -51]) := List.countP_append (p := literal q) (l₁ := [-3, -4, -6, -10, -12, -14, -16, -17, -18, -21, -22, -25]) (l₂ := [-27, -28, -31, -33, -34, -36, -38, -41, -43, -45, -48, -50, -51])
  have hm := merge_right (literal (valuationOf q) (781)) (literal (valuationOf q) (792)) (countLit q [-3, -4, -6, -10, -12, -14, -16, -17, -18, -21, -22, -25]) (countLit q [-27, -28, -31, -33, -34, -36, -38, -41, -43, -45, -48, -50, -51]) (count787 q) 6 (meaning781 q) (meaning792 q) hs
  change valuationOf q 781 = false ∨ valuationOf q 792 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause622 (q : Snake 81) (h : Conditions q) : valuation q 781 = false ∨ valuation q 792 = true := counterClause622 (baseVal q)

theorem counterClause623 (q : Nat → Bool) : valuationOf q 729 = false ∨ valuationOf q 778 = false ∨ valuationOf q 790 = true := by
  have hs : count787 q = (countLit q [-3, -4, -6, -10, -12, -14, -16, -17, -18, -21, -22, -25]) + (countLit q [-27, -28, -31, -33, -34, -36, -38, -41, -43, -45, -48, -50, -51]) := List.countP_append (p := literal q) (l₁ := [-3, -4, -6, -10, -12, -14, -16, -17, -18, -21, -22, -25]) (l₂ := [-27, -28, -31, -33, -34, -36, -38, -41, -43, -45, -48, -50, -51])
  have hm := merge_two (literal (valuationOf q) (729)) (literal (valuationOf q) (778)) (literal (valuationOf q) (790)) (countLit q [-3, -4, -6, -10, -12, -14, -16, -17, -18, -21, -22, -25]) (countLit q [-27, -28, -31, -33, -34, -36, -38, -41, -43, -45, -48, -50, -51]) (count787 q) 1 3 (meaning729 q) (meaning778 q) (meaning790 q) hs
  change valuationOf q 729 = false ∨ valuationOf q 778 = false ∨ valuationOf q 790 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause623 (q : Snake 81) (h : Conditions q) : valuation q 729 = false ∨ valuation q 778 = false ∨ valuation q 790 = true := counterClause623 (baseVal q)

theorem counterClause624 (q : Nat → Bool) : valuationOf q 729 = false ∨ valuationOf q 779 = false ∨ valuationOf q 791 = true := by
  have hs : count787 q = (countLit q [-3, -4, -6, -10, -12, -14, -16, -17, -18, -21, -22, -25]) + (countLit q [-27, -28, -31, -33, -34, -36, -38, -41, -43, -45, -48, -50, -51]) := List.countP_append (p := literal q) (l₁ := [-3, -4, -6, -10, -12, -14, -16, -17, -18, -21, -22, -25]) (l₂ := [-27, -28, -31, -33, -34, -36, -38, -41, -43, -45, -48, -50, -51])
  have hm := merge_two (literal (valuationOf q) (729)) (literal (valuationOf q) (779)) (literal (valuationOf q) (791)) (countLit q [-3, -4, -6, -10, -12, -14, -16, -17, -18, -21, -22, -25]) (countLit q [-27, -28, -31, -33, -34, -36, -38, -41, -43, -45, -48, -50, -51]) (count787 q) 1 4 (meaning729 q) (meaning779 q) (meaning791 q) hs
  change valuationOf q 729 = false ∨ valuationOf q 779 = false ∨ valuationOf q 791 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause624 (q : Snake 81) (h : Conditions q) : valuation q 729 = false ∨ valuation q 779 = false ∨ valuation q 791 = true := counterClause624 (baseVal q)

theorem counterClause625 (q : Nat → Bool) : valuationOf q 729 = false ∨ valuationOf q 780 = false ∨ valuationOf q 792 = true := by
  have hs : count787 q = (countLit q [-3, -4, -6, -10, -12, -14, -16, -17, -18, -21, -22, -25]) + (countLit q [-27, -28, -31, -33, -34, -36, -38, -41, -43, -45, -48, -50, -51]) := List.countP_append (p := literal q) (l₁ := [-3, -4, -6, -10, -12, -14, -16, -17, -18, -21, -22, -25]) (l₂ := [-27, -28, -31, -33, -34, -36, -38, -41, -43, -45, -48, -50, -51])
  have hm := merge_two (literal (valuationOf q) (729)) (literal (valuationOf q) (780)) (literal (valuationOf q) (792)) (countLit q [-3, -4, -6, -10, -12, -14, -16, -17, -18, -21, -22, -25]) (countLit q [-27, -28, -31, -33, -34, -36, -38, -41, -43, -45, -48, -50, -51]) (count787 q) 1 5 (meaning729 q) (meaning780 q) (meaning792 q) hs
  change valuationOf q 729 = false ∨ valuationOf q 780 = false ∨ valuationOf q 792 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause625 (q : Snake 81) (h : Conditions q) : valuation q 729 = false ∨ valuation q 780 = false ∨ valuation q 792 = true := counterClause625 (baseVal q)

theorem counterClause626 (q : Nat → Bool) : valuationOf q 730 = false ∨ valuationOf q 776 = false ∨ valuationOf q 789 = true := by
  have hs : count787 q = (countLit q [-3, -4, -6, -10, -12, -14, -16, -17, -18, -21, -22, -25]) + (countLit q [-27, -28, -31, -33, -34, -36, -38, -41, -43, -45, -48, -50, -51]) := List.countP_append (p := literal q) (l₁ := [-3, -4, -6, -10, -12, -14, -16, -17, -18, -21, -22, -25]) (l₂ := [-27, -28, -31, -33, -34, -36, -38, -41, -43, -45, -48, -50, -51])
  have hm := merge_two (literal (valuationOf q) (730)) (literal (valuationOf q) (776)) (literal (valuationOf q) (789)) (countLit q [-3, -4, -6, -10, -12, -14, -16, -17, -18, -21, -22, -25]) (countLit q [-27, -28, -31, -33, -34, -36, -38, -41, -43, -45, -48, -50, -51]) (count787 q) 2 1 (meaning730 q) (meaning776 q) (meaning789 q) hs
  change valuationOf q 730 = false ∨ valuationOf q 776 = false ∨ valuationOf q 789 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause626 (q : Snake 81) (h : Conditions q) : valuation q 730 = false ∨ valuation q 776 = false ∨ valuation q 789 = true := counterClause626 (baseVal q)

theorem counterClause627 (q : Nat → Bool) : valuationOf q 730 = false ∨ valuationOf q 777 = false ∨ valuationOf q 790 = true := by
  have hs : count787 q = (countLit q [-3, -4, -6, -10, -12, -14, -16, -17, -18, -21, -22, -25]) + (countLit q [-27, -28, -31, -33, -34, -36, -38, -41, -43, -45, -48, -50, -51]) := List.countP_append (p := literal q) (l₁ := [-3, -4, -6, -10, -12, -14, -16, -17, -18, -21, -22, -25]) (l₂ := [-27, -28, -31, -33, -34, -36, -38, -41, -43, -45, -48, -50, -51])
  have hm := merge_two (literal (valuationOf q) (730)) (literal (valuationOf q) (777)) (literal (valuationOf q) (790)) (countLit q [-3, -4, -6, -10, -12, -14, -16, -17, -18, -21, -22, -25]) (countLit q [-27, -28, -31, -33, -34, -36, -38, -41, -43, -45, -48, -50, -51]) (count787 q) 2 2 (meaning730 q) (meaning777 q) (meaning790 q) hs
  change valuationOf q 730 = false ∨ valuationOf q 777 = false ∨ valuationOf q 790 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause627 (q : Snake 81) (h : Conditions q) : valuation q 730 = false ∨ valuation q 777 = false ∨ valuation q 790 = true := counterClause627 (baseVal q)

theorem counterClause628 (q : Nat → Bool) : valuationOf q 730 = false ∨ valuationOf q 778 = false ∨ valuationOf q 791 = true := by
  have hs : count787 q = (countLit q [-3, -4, -6, -10, -12, -14, -16, -17, -18, -21, -22, -25]) + (countLit q [-27, -28, -31, -33, -34, -36, -38, -41, -43, -45, -48, -50, -51]) := List.countP_append (p := literal q) (l₁ := [-3, -4, -6, -10, -12, -14, -16, -17, -18, -21, -22, -25]) (l₂ := [-27, -28, -31, -33, -34, -36, -38, -41, -43, -45, -48, -50, -51])
  have hm := merge_two (literal (valuationOf q) (730)) (literal (valuationOf q) (778)) (literal (valuationOf q) (791)) (countLit q [-3, -4, -6, -10, -12, -14, -16, -17, -18, -21, -22, -25]) (countLit q [-27, -28, -31, -33, -34, -36, -38, -41, -43, -45, -48, -50, -51]) (count787 q) 2 3 (meaning730 q) (meaning778 q) (meaning791 q) hs
  change valuationOf q 730 = false ∨ valuationOf q 778 = false ∨ valuationOf q 791 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause628 (q : Snake 81) (h : Conditions q) : valuation q 730 = false ∨ valuation q 778 = false ∨ valuation q 791 = true := counterClause628 (baseVal q)

theorem counterClause629 (q : Nat → Bool) : valuationOf q 730 = false ∨ valuationOf q 779 = false ∨ valuationOf q 792 = true := by
  have hs : count787 q = (countLit q [-3, -4, -6, -10, -12, -14, -16, -17, -18, -21, -22, -25]) + (countLit q [-27, -28, -31, -33, -34, -36, -38, -41, -43, -45, -48, -50, -51]) := List.countP_append (p := literal q) (l₁ := [-3, -4, -6, -10, -12, -14, -16, -17, -18, -21, -22, -25]) (l₂ := [-27, -28, -31, -33, -34, -36, -38, -41, -43, -45, -48, -50, -51])
  have hm := merge_two (literal (valuationOf q) (730)) (literal (valuationOf q) (779)) (literal (valuationOf q) (792)) (countLit q [-3, -4, -6, -10, -12, -14, -16, -17, -18, -21, -22, -25]) (countLit q [-27, -28, -31, -33, -34, -36, -38, -41, -43, -45, -48, -50, -51]) (count787 q) 2 4 (meaning730 q) (meaning779 q) (meaning792 q) hs
  change valuationOf q 730 = false ∨ valuationOf q 779 = false ∨ valuationOf q 792 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause629 (q : Snake 81) (h : Conditions q) : valuation q 730 = false ∨ valuation q 779 = false ∨ valuation q 792 = true := counterClause629 (baseVal q)

theorem counterClause630 (q : Nat → Bool) : valuationOf q 730 = false ∨ valuationOf q 780 = false ∨ valuationOf q 793 = true := by
  have hs : count787 q = (countLit q [-3, -4, -6, -10, -12, -14, -16, -17, -18, -21, -22, -25]) + (countLit q [-27, -28, -31, -33, -34, -36, -38, -41, -43, -45, -48, -50, -51]) := List.countP_append (p := literal q) (l₁ := [-3, -4, -6, -10, -12, -14, -16, -17, -18, -21, -22, -25]) (l₂ := [-27, -28, -31, -33, -34, -36, -38, -41, -43, -45, -48, -50, -51])
  have hm := merge_two (literal (valuationOf q) (730)) (literal (valuationOf q) (780)) (literal (valuationOf q) (793)) (countLit q [-3, -4, -6, -10, -12, -14, -16, -17, -18, -21, -22, -25]) (countLit q [-27, -28, -31, -33, -34, -36, -38, -41, -43, -45, -48, -50, -51]) (count787 q) 2 5 (meaning730 q) (meaning780 q) (meaning793 q) hs
  change valuationOf q 730 = false ∨ valuationOf q 780 = false ∨ valuationOf q 793 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause630 (q : Snake 81) (h : Conditions q) : valuation q 730 = false ∨ valuation q 780 = false ∨ valuation q 793 = true := counterClause630 (baseVal q)

theorem counterClause631 (q : Nat → Bool) : valuationOf q 731 = false ∨ valuationOf q 789 = true := by
  have hs : count787 q = (countLit q [-3, -4, -6, -10, -12, -14, -16, -17, -18, -21, -22, -25]) + (countLit q [-27, -28, -31, -33, -34, -36, -38, -41, -43, -45, -48, -50, -51]) := List.countP_append (p := literal q) (l₁ := [-3, -4, -6, -10, -12, -14, -16, -17, -18, -21, -22, -25]) (l₂ := [-27, -28, -31, -33, -34, -36, -38, -41, -43, -45, -48, -50, -51])
  have hm := merge_left (literal (valuationOf q) (731)) (literal (valuationOf q) (789)) (countLit q [-3, -4, -6, -10, -12, -14, -16, -17, -18, -21, -22, -25]) (countLit q [-27, -28, -31, -33, -34, -36, -38, -41, -43, -45, -48, -50, -51]) (count787 q) 3 (meaning731 q) (meaning789 q) hs
  change valuationOf q 731 = false ∨ valuationOf q 789 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause631 (q : Snake 81) (h : Conditions q) : valuation q 731 = false ∨ valuation q 789 = true := counterClause631 (baseVal q)

theorem counterClause632 (q : Nat → Bool) : valuationOf q 731 = false ∨ valuationOf q 776 = false ∨ valuationOf q 790 = true := by
  have hs : count787 q = (countLit q [-3, -4, -6, -10, -12, -14, -16, -17, -18, -21, -22, -25]) + (countLit q [-27, -28, -31, -33, -34, -36, -38, -41, -43, -45, -48, -50, -51]) := List.countP_append (p := literal q) (l₁ := [-3, -4, -6, -10, -12, -14, -16, -17, -18, -21, -22, -25]) (l₂ := [-27, -28, -31, -33, -34, -36, -38, -41, -43, -45, -48, -50, -51])
  have hm := merge_two (literal (valuationOf q) (731)) (literal (valuationOf q) (776)) (literal (valuationOf q) (790)) (countLit q [-3, -4, -6, -10, -12, -14, -16, -17, -18, -21, -22, -25]) (countLit q [-27, -28, -31, -33, -34, -36, -38, -41, -43, -45, -48, -50, -51]) (count787 q) 3 1 (meaning731 q) (meaning776 q) (meaning790 q) hs
  change valuationOf q 731 = false ∨ valuationOf q 776 = false ∨ valuationOf q 790 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause632 (q : Snake 81) (h : Conditions q) : valuation q 731 = false ∨ valuation q 776 = false ∨ valuation q 790 = true := counterClause632 (baseVal q)

theorem counterClause633 (q : Nat → Bool) : valuationOf q 731 = false ∨ valuationOf q 777 = false ∨ valuationOf q 791 = true := by
  have hs : count787 q = (countLit q [-3, -4, -6, -10, -12, -14, -16, -17, -18, -21, -22, -25]) + (countLit q [-27, -28, -31, -33, -34, -36, -38, -41, -43, -45, -48, -50, -51]) := List.countP_append (p := literal q) (l₁ := [-3, -4, -6, -10, -12, -14, -16, -17, -18, -21, -22, -25]) (l₂ := [-27, -28, -31, -33, -34, -36, -38, -41, -43, -45, -48, -50, -51])
  have hm := merge_two (literal (valuationOf q) (731)) (literal (valuationOf q) (777)) (literal (valuationOf q) (791)) (countLit q [-3, -4, -6, -10, -12, -14, -16, -17, -18, -21, -22, -25]) (countLit q [-27, -28, -31, -33, -34, -36, -38, -41, -43, -45, -48, -50, -51]) (count787 q) 3 2 (meaning731 q) (meaning777 q) (meaning791 q) hs
  change valuationOf q 731 = false ∨ valuationOf q 777 = false ∨ valuationOf q 791 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause633 (q : Snake 81) (h : Conditions q) : valuation q 731 = false ∨ valuation q 777 = false ∨ valuation q 791 = true := counterClause633 (baseVal q)

theorem counterClause634 (q : Nat → Bool) : valuationOf q 731 = false ∨ valuationOf q 778 = false ∨ valuationOf q 792 = true := by
  have hs : count787 q = (countLit q [-3, -4, -6, -10, -12, -14, -16, -17, -18, -21, -22, -25]) + (countLit q [-27, -28, -31, -33, -34, -36, -38, -41, -43, -45, -48, -50, -51]) := List.countP_append (p := literal q) (l₁ := [-3, -4, -6, -10, -12, -14, -16, -17, -18, -21, -22, -25]) (l₂ := [-27, -28, -31, -33, -34, -36, -38, -41, -43, -45, -48, -50, -51])
  have hm := merge_two (literal (valuationOf q) (731)) (literal (valuationOf q) (778)) (literal (valuationOf q) (792)) (countLit q [-3, -4, -6, -10, -12, -14, -16, -17, -18, -21, -22, -25]) (countLit q [-27, -28, -31, -33, -34, -36, -38, -41, -43, -45, -48, -50, -51]) (count787 q) 3 3 (meaning731 q) (meaning778 q) (meaning792 q) hs
  change valuationOf q 731 = false ∨ valuationOf q 778 = false ∨ valuationOf q 792 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause634 (q : Snake 81) (h : Conditions q) : valuation q 731 = false ∨ valuation q 778 = false ∨ valuation q 792 = true := counterClause634 (baseVal q)

theorem counterClause635 (q : Nat → Bool) : valuationOf q 731 = false ∨ valuationOf q 779 = false ∨ valuationOf q 793 = true := by
  have hs : count787 q = (countLit q [-3, -4, -6, -10, -12, -14, -16, -17, -18, -21, -22, -25]) + (countLit q [-27, -28, -31, -33, -34, -36, -38, -41, -43, -45, -48, -50, -51]) := List.countP_append (p := literal q) (l₁ := [-3, -4, -6, -10, -12, -14, -16, -17, -18, -21, -22, -25]) (l₂ := [-27, -28, -31, -33, -34, -36, -38, -41, -43, -45, -48, -50, -51])
  have hm := merge_two (literal (valuationOf q) (731)) (literal (valuationOf q) (779)) (literal (valuationOf q) (793)) (countLit q [-3, -4, -6, -10, -12, -14, -16, -17, -18, -21, -22, -25]) (countLit q [-27, -28, -31, -33, -34, -36, -38, -41, -43, -45, -48, -50, -51]) (count787 q) 3 4 (meaning731 q) (meaning779 q) (meaning793 q) hs
  change valuationOf q 731 = false ∨ valuationOf q 779 = false ∨ valuationOf q 793 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause635 (q : Snake 81) (h : Conditions q) : valuation q 731 = false ∨ valuation q 779 = false ∨ valuation q 793 = true := counterClause635 (baseVal q)

theorem counterClause636 (q : Nat → Bool) : valuationOf q 731 = false ∨ valuationOf q 781 = false ∨ valuationOf q 795 = true := by
  have hs : count787 q = (countLit q [-3, -4, -6, -10, -12, -14, -16, -17, -18, -21, -22, -25]) + (countLit q [-27, -28, -31, -33, -34, -36, -38, -41, -43, -45, -48, -50, -51]) := List.countP_append (p := literal q) (l₁ := [-3, -4, -6, -10, -12, -14, -16, -17, -18, -21, -22, -25]) (l₂ := [-27, -28, -31, -33, -34, -36, -38, -41, -43, -45, -48, -50, -51])
  have hm := merge_two (literal (valuationOf q) (731)) (literal (valuationOf q) (781)) (literal (valuationOf q) (795)) (countLit q [-3, -4, -6, -10, -12, -14, -16, -17, -18, -21, -22, -25]) (countLit q [-27, -28, -31, -33, -34, -36, -38, -41, -43, -45, -48, -50, -51]) (count787 q) 3 6 (meaning731 q) (meaning781 q) (meaning795 q) hs
  change valuationOf q 731 = false ∨ valuationOf q 781 = false ∨ valuationOf q 795 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause636 (q : Snake 81) (h : Conditions q) : valuation q 731 = false ∨ valuation q 781 = false ∨ valuation q 795 = true := counterClause636 (baseVal q)

theorem counterClause637 (q : Nat → Bool) : valuationOf q 732 = false ∨ valuationOf q 776 = false ∨ valuationOf q 791 = true := by
  have hs : count787 q = (countLit q [-3, -4, -6, -10, -12, -14, -16, -17, -18, -21, -22, -25]) + (countLit q [-27, -28, -31, -33, -34, -36, -38, -41, -43, -45, -48, -50, -51]) := List.countP_append (p := literal q) (l₁ := [-3, -4, -6, -10, -12, -14, -16, -17, -18, -21, -22, -25]) (l₂ := [-27, -28, -31, -33, -34, -36, -38, -41, -43, -45, -48, -50, -51])
  have hm := merge_two (literal (valuationOf q) (732)) (literal (valuationOf q) (776)) (literal (valuationOf q) (791)) (countLit q [-3, -4, -6, -10, -12, -14, -16, -17, -18, -21, -22, -25]) (countLit q [-27, -28, -31, -33, -34, -36, -38, -41, -43, -45, -48, -50, -51]) (count787 q) 4 1 (meaning732 q) (meaning776 q) (meaning791 q) hs
  change valuationOf q 732 = false ∨ valuationOf q 776 = false ∨ valuationOf q 791 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause637 (q : Snake 81) (h : Conditions q) : valuation q 732 = false ∨ valuation q 776 = false ∨ valuation q 791 = true := counterClause637 (baseVal q)

theorem counterClause638 (q : Nat → Bool) : valuationOf q 732 = false ∨ valuationOf q 777 = false ∨ valuationOf q 792 = true := by
  have hs : count787 q = (countLit q [-3, -4, -6, -10, -12, -14, -16, -17, -18, -21, -22, -25]) + (countLit q [-27, -28, -31, -33, -34, -36, -38, -41, -43, -45, -48, -50, -51]) := List.countP_append (p := literal q) (l₁ := [-3, -4, -6, -10, -12, -14, -16, -17, -18, -21, -22, -25]) (l₂ := [-27, -28, -31, -33, -34, -36, -38, -41, -43, -45, -48, -50, -51])
  have hm := merge_two (literal (valuationOf q) (732)) (literal (valuationOf q) (777)) (literal (valuationOf q) (792)) (countLit q [-3, -4, -6, -10, -12, -14, -16, -17, -18, -21, -22, -25]) (countLit q [-27, -28, -31, -33, -34, -36, -38, -41, -43, -45, -48, -50, -51]) (count787 q) 4 2 (meaning732 q) (meaning777 q) (meaning792 q) hs
  change valuationOf q 732 = false ∨ valuationOf q 777 = false ∨ valuationOf q 792 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause638 (q : Snake 81) (h : Conditions q) : valuation q 732 = false ∨ valuation q 777 = false ∨ valuation q 792 = true := counterClause638 (baseVal q)

theorem counterClause639 (q : Nat → Bool) : valuationOf q 732 = false ∨ valuationOf q 778 = false ∨ valuationOf q 793 = true := by
  have hs : count787 q = (countLit q [-3, -4, -6, -10, -12, -14, -16, -17, -18, -21, -22, -25]) + (countLit q [-27, -28, -31, -33, -34, -36, -38, -41, -43, -45, -48, -50, -51]) := List.countP_append (p := literal q) (l₁ := [-3, -4, -6, -10, -12, -14, -16, -17, -18, -21, -22, -25]) (l₂ := [-27, -28, -31, -33, -34, -36, -38, -41, -43, -45, -48, -50, -51])
  have hm := merge_two (literal (valuationOf q) (732)) (literal (valuationOf q) (778)) (literal (valuationOf q) (793)) (countLit q [-3, -4, -6, -10, -12, -14, -16, -17, -18, -21, -22, -25]) (countLit q [-27, -28, -31, -33, -34, -36, -38, -41, -43, -45, -48, -50, -51]) (count787 q) 4 3 (meaning732 q) (meaning778 q) (meaning793 q) hs
  change valuationOf q 732 = false ∨ valuationOf q 778 = false ∨ valuationOf q 793 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause639 (q : Snake 81) (h : Conditions q) : valuation q 732 = false ∨ valuation q 778 = false ∨ valuation q 793 = true := counterClause639 (baseVal q)

theorem counterClause640 (q : Nat → Bool) : valuationOf q 732 = false ∨ valuationOf q 779 = false ∨ valuationOf q 794 = true := by
  have hs : count787 q = (countLit q [-3, -4, -6, -10, -12, -14, -16, -17, -18, -21, -22, -25]) + (countLit q [-27, -28, -31, -33, -34, -36, -38, -41, -43, -45, -48, -50, -51]) := List.countP_append (p := literal q) (l₁ := [-3, -4, -6, -10, -12, -14, -16, -17, -18, -21, -22, -25]) (l₂ := [-27, -28, -31, -33, -34, -36, -38, -41, -43, -45, -48, -50, -51])
  have hm := merge_two (literal (valuationOf q) (732)) (literal (valuationOf q) (779)) (literal (valuationOf q) (794)) (countLit q [-3, -4, -6, -10, -12, -14, -16, -17, -18, -21, -22, -25]) (countLit q [-27, -28, -31, -33, -34, -36, -38, -41, -43, -45, -48, -50, -51]) (count787 q) 4 4 (meaning732 q) (meaning779 q) (meaning794 q) hs
  change valuationOf q 732 = false ∨ valuationOf q 779 = false ∨ valuationOf q 794 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause640 (q : Snake 81) (h : Conditions q) : valuation q 732 = false ∨ valuation q 779 = false ∨ valuation q 794 = true := counterClause640 (baseVal q)

theorem block19 (q : Snake 81) (h : Conditions q) : B112E174.Block19 (valuation q) :=
  ⟨clause609 q h, clause610 q h, clause611 q h, clause612 q h, clause613 q h, clause614 q h, clause615 q h, clause616 q h, clause617 q h, clause618 q h, clause619 q h, clause620 q h, clause621 q h, clause622 q h, clause623 q h, clause624 q h, clause625 q h, clause626 q h, clause627 q h, clause628 q h, clause629 q h, clause630 q h, clause631 q h, clause632 q h, clause633 q h, clause634 q h, clause635 q h, clause636 q h, clause637 q h, clause638 q h, clause639 q h, clause640 q h⟩

end
end Snake9.Regrowth.E112174
