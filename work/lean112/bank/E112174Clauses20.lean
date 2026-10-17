import E112174Semantics
import B112E174Inputs
namespace Snake9.Regrowth.E112174
noncomputable section
local instance blockDec20 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause641 (q : Nat → Bool) : valuationOf q 733 = false ∨ valuationOf q 776 = false ∨ valuationOf q 792 = true := by
  have hs : count787 q = (countLit q [-3, -4, -6, -10, -12, -14, -16, -17, -18, -21, -22, -25]) + (countLit q [-27, -28, -31, -33, -34, -36, -38, -41, -43, -45, -48, -50, -51]) := List.countP_append (p := literal q) (l₁ := [-3, -4, -6, -10, -12, -14, -16, -17, -18, -21, -22, -25]) (l₂ := [-27, -28, -31, -33, -34, -36, -38, -41, -43, -45, -48, -50, -51])
  have hm := merge_two (literal (valuationOf q) (733)) (literal (valuationOf q) (776)) (literal (valuationOf q) (792)) (countLit q [-3, -4, -6, -10, -12, -14, -16, -17, -18, -21, -22, -25]) (countLit q [-27, -28, -31, -33, -34, -36, -38, -41, -43, -45, -48, -50, -51]) (count787 q) 5 1 (meaning733 q) (meaning776 q) (meaning792 q) hs
  change valuationOf q 733 = false ∨ valuationOf q 776 = false ∨ valuationOf q 792 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause641 (q : Snake 81) (h : Conditions q) : valuation q 733 = false ∨ valuation q 776 = false ∨ valuation q 792 = true := counterClause641 (baseVal q)

theorem counterClause642 (q : Nat → Bool) : valuationOf q 733 = false ∨ valuationOf q 777 = false ∨ valuationOf q 793 = true := by
  have hs : count787 q = (countLit q [-3, -4, -6, -10, -12, -14, -16, -17, -18, -21, -22, -25]) + (countLit q [-27, -28, -31, -33, -34, -36, -38, -41, -43, -45, -48, -50, -51]) := List.countP_append (p := literal q) (l₁ := [-3, -4, -6, -10, -12, -14, -16, -17, -18, -21, -22, -25]) (l₂ := [-27, -28, -31, -33, -34, -36, -38, -41, -43, -45, -48, -50, -51])
  have hm := merge_two (literal (valuationOf q) (733)) (literal (valuationOf q) (777)) (literal (valuationOf q) (793)) (countLit q [-3, -4, -6, -10, -12, -14, -16, -17, -18, -21, -22, -25]) (countLit q [-27, -28, -31, -33, -34, -36, -38, -41, -43, -45, -48, -50, -51]) (count787 q) 5 2 (meaning733 q) (meaning777 q) (meaning793 q) hs
  change valuationOf q 733 = false ∨ valuationOf q 777 = false ∨ valuationOf q 793 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause642 (q : Snake 81) (h : Conditions q) : valuation q 733 = false ∨ valuation q 777 = false ∨ valuation q 793 = true := counterClause642 (baseVal q)

theorem counterClause643 (q : Nat → Bool) : valuationOf q 733 = false ∨ valuationOf q 779 = false ∨ valuationOf q 795 = true := by
  have hs : count787 q = (countLit q [-3, -4, -6, -10, -12, -14, -16, -17, -18, -21, -22, -25]) + (countLit q [-27, -28, -31, -33, -34, -36, -38, -41, -43, -45, -48, -50, -51]) := List.countP_append (p := literal q) (l₁ := [-3, -4, -6, -10, -12, -14, -16, -17, -18, -21, -22, -25]) (l₂ := [-27, -28, -31, -33, -34, -36, -38, -41, -43, -45, -48, -50, -51])
  have hm := merge_two (literal (valuationOf q) (733)) (literal (valuationOf q) (779)) (literal (valuationOf q) (795)) (countLit q [-3, -4, -6, -10, -12, -14, -16, -17, -18, -21, -22, -25]) (countLit q [-27, -28, -31, -33, -34, -36, -38, -41, -43, -45, -48, -50, -51]) (count787 q) 5 4 (meaning733 q) (meaning779 q) (meaning795 q) hs
  change valuationOf q 733 = false ∨ valuationOf q 779 = false ∨ valuationOf q 795 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause643 (q : Snake 81) (h : Conditions q) : valuation q 733 = false ∨ valuation q 779 = false ∨ valuation q 795 = true := counterClause643 (baseVal q)

theorem counterClause644 (q : Nat → Bool) : valuationOf q 734 = false ∨ valuationOf q 792 = true := by
  have hs : count787 q = (countLit q [-3, -4, -6, -10, -12, -14, -16, -17, -18, -21, -22, -25]) + (countLit q [-27, -28, -31, -33, -34, -36, -38, -41, -43, -45, -48, -50, -51]) := List.countP_append (p := literal q) (l₁ := [-3, -4, -6, -10, -12, -14, -16, -17, -18, -21, -22, -25]) (l₂ := [-27, -28, -31, -33, -34, -36, -38, -41, -43, -45, -48, -50, -51])
  have hm := merge_left (literal (valuationOf q) (734)) (literal (valuationOf q) (792)) (countLit q [-3, -4, -6, -10, -12, -14, -16, -17, -18, -21, -22, -25]) (countLit q [-27, -28, -31, -33, -34, -36, -38, -41, -43, -45, -48, -50, -51]) (count787 q) 6 (meaning734 q) (meaning792 q) hs
  change valuationOf q 734 = false ∨ valuationOf q 792 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause644 (q : Snake 81) (h : Conditions q) : valuation q 734 = false ∨ valuation q 792 = true := counterClause644 (baseVal q)

theorem counterClause645 (q : Nat → Bool) : valuationOf q 734 = false ∨ valuationOf q 776 = false ∨ valuationOf q 793 = true := by
  have hs : count787 q = (countLit q [-3, -4, -6, -10, -12, -14, -16, -17, -18, -21, -22, -25]) + (countLit q [-27, -28, -31, -33, -34, -36, -38, -41, -43, -45, -48, -50, -51]) := List.countP_append (p := literal q) (l₁ := [-3, -4, -6, -10, -12, -14, -16, -17, -18, -21, -22, -25]) (l₂ := [-27, -28, -31, -33, -34, -36, -38, -41, -43, -45, -48, -50, -51])
  have hm := merge_two (literal (valuationOf q) (734)) (literal (valuationOf q) (776)) (literal (valuationOf q) (793)) (countLit q [-3, -4, -6, -10, -12, -14, -16, -17, -18, -21, -22, -25]) (countLit q [-27, -28, -31, -33, -34, -36, -38, -41, -43, -45, -48, -50, -51]) (count787 q) 6 1 (meaning734 q) (meaning776 q) (meaning793 q) hs
  change valuationOf q 734 = false ∨ valuationOf q 776 = false ∨ valuationOf q 793 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause645 (q : Snake 81) (h : Conditions q) : valuation q 734 = false ∨ valuation q 776 = false ∨ valuation q 793 = true := counterClause645 (baseVal q)

theorem counterClause646 (q : Nat → Bool) : valuationOf q 734 = false ∨ valuationOf q 778 = false ∨ valuationOf q 795 = true := by
  have hs : count787 q = (countLit q [-3, -4, -6, -10, -12, -14, -16, -17, -18, -21, -22, -25]) + (countLit q [-27, -28, -31, -33, -34, -36, -38, -41, -43, -45, -48, -50, -51]) := List.countP_append (p := literal q) (l₁ := [-3, -4, -6, -10, -12, -14, -16, -17, -18, -21, -22, -25]) (l₂ := [-27, -28, -31, -33, -34, -36, -38, -41, -43, -45, -48, -50, -51])
  have hm := merge_two (literal (valuationOf q) (734)) (literal (valuationOf q) (778)) (literal (valuationOf q) (795)) (countLit q [-3, -4, -6, -10, -12, -14, -16, -17, -18, -21, -22, -25]) (countLit q [-27, -28, -31, -33, -34, -36, -38, -41, -43, -45, -48, -50, -51]) (count787 q) 6 3 (meaning734 q) (meaning778 q) (meaning795 q) hs
  change valuationOf q 734 = false ∨ valuationOf q 778 = false ∨ valuationOf q 795 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause646 (q : Snake 81) (h : Conditions q) : valuation q 734 = false ∨ valuation q 778 = false ∨ valuation q 795 = true := counterClause646 (baseVal q)

theorem counterClause647 (q : Nat → Bool) : valuationOf q 58 = true ∨ valuationOf q 798 = true := by
  have hs : count798 q = (countLit q [-56]) + (countLit q [-58]) := List.countP_append (p := literal q) (l₁ := [-56]) (l₂ := [-58])
  have hm := merge_right (literal (valuationOf q) (-58)) (literal (valuationOf q) (798)) (countLit q [-56]) (countLit q [-58]) (count798 q) 1 (meaningNeg58 q) (meaning798 q) hs
  change (! (valuationOf q 58)) = false ∨ valuationOf q 798 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause647 (q : Snake 81) (h : Conditions q) : valuation q 58 = true ∨ valuation q 798 = true := counterClause647 (baseVal q)

theorem counterClause648 (q : Nat → Bool) : valuationOf q 56 = true ∨ valuationOf q 798 = true := by
  have hs : count798 q = (countLit q [-56]) + (countLit q [-58]) := List.countP_append (p := literal q) (l₁ := [-56]) (l₂ := [-58])
  have hm := merge_left (literal (valuationOf q) (-56)) (literal (valuationOf q) (798)) (countLit q [-56]) (countLit q [-58]) (count798 q) 1 (meaningNeg56 q) (meaning798 q) hs
  change (! (valuationOf q 56)) = false ∨ valuationOf q 798 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause648 (q : Snake 81) (h : Conditions q) : valuation q 56 = true ∨ valuation q 798 = true := counterClause648 (baseVal q)

theorem counterClause649 (q : Nat → Bool) : valuationOf q 56 = true ∨ valuationOf q 58 = true ∨ valuationOf q 799 = true := by
  have hs : count798 q = (countLit q [-56]) + (countLit q [-58]) := List.countP_append (p := literal q) (l₁ := [-56]) (l₂ := [-58])
  have hm := merge_two (literal (valuationOf q) (-56)) (literal (valuationOf q) (-58)) (literal (valuationOf q) (799)) (countLit q [-56]) (countLit q [-58]) (count798 q) 1 1 (meaningNeg56 q) (meaningNeg58 q) (meaning799 q) hs
  change (! (valuationOf q 56)) = false ∨ (! (valuationOf q 58)) = false ∨ valuationOf q 799 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause649 (q : Snake 81) (h : Conditions q) : valuation q 56 = true ∨ valuation q 58 = true ∨ valuation q 799 = true := counterClause649 (baseVal q)

theorem counterClause650 (q : Nat → Bool) : valuationOf q 798 = false ∨ valuationOf q 800 = true := by
  have hs : count800 q = (countLit q [-53]) + (countLit q [-56, -58]) := List.countP_append (p := literal q) (l₁ := [-53]) (l₂ := [-56, -58])
  have hm := merge_right (literal (valuationOf q) (798)) (literal (valuationOf q) (800)) (countLit q [-53]) (countLit q [-56, -58]) (count800 q) 1 (meaning798 q) (meaning800 q) hs
  change valuationOf q 798 = false ∨ valuationOf q 800 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause650 (q : Snake 81) (h : Conditions q) : valuation q 798 = false ∨ valuation q 800 = true := counterClause650 (baseVal q)

theorem counterClause651 (q : Nat → Bool) : valuationOf q 799 = false ∨ valuationOf q 801 = true := by
  have hs : count800 q = (countLit q [-53]) + (countLit q [-56, -58]) := List.countP_append (p := literal q) (l₁ := [-53]) (l₂ := [-56, -58])
  have hm := merge_right (literal (valuationOf q) (799)) (literal (valuationOf q) (801)) (countLit q [-53]) (countLit q [-56, -58]) (count800 q) 2 (meaning799 q) (meaning801 q) hs
  change valuationOf q 799 = false ∨ valuationOf q 801 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause651 (q : Snake 81) (h : Conditions q) : valuation q 799 = false ∨ valuation q 801 = true := counterClause651 (baseVal q)

theorem counterClause652 (q : Nat → Bool) : valuationOf q 53 = true ∨ valuationOf q 800 = true := by
  have hs : count800 q = (countLit q [-53]) + (countLit q [-56, -58]) := List.countP_append (p := literal q) (l₁ := [-53]) (l₂ := [-56, -58])
  have hm := merge_left (literal (valuationOf q) (-53)) (literal (valuationOf q) (800)) (countLit q [-53]) (countLit q [-56, -58]) (count800 q) 1 (meaningNeg53 q) (meaning800 q) hs
  change (! (valuationOf q 53)) = false ∨ valuationOf q 800 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause652 (q : Snake 81) (h : Conditions q) : valuation q 53 = true ∨ valuation q 800 = true := counterClause652 (baseVal q)

theorem counterClause653 (q : Nat → Bool) : valuationOf q 53 = true ∨ valuationOf q 798 = false ∨ valuationOf q 801 = true := by
  have hs : count800 q = (countLit q [-53]) + (countLit q [-56, -58]) := List.countP_append (p := literal q) (l₁ := [-53]) (l₂ := [-56, -58])
  have hm := merge_two (literal (valuationOf q) (-53)) (literal (valuationOf q) (798)) (literal (valuationOf q) (801)) (countLit q [-53]) (countLit q [-56, -58]) (count800 q) 1 1 (meaningNeg53 q) (meaning798 q) (meaning801 q) hs
  change (! (valuationOf q 53)) = false ∨ valuationOf q 798 = false ∨ valuationOf q 801 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause653 (q : Snake 81) (h : Conditions q) : valuation q 53 = true ∨ valuation q 798 = false ∨ valuation q 801 = true := counterClause653 (baseVal q)

theorem counterClause654 (q : Nat → Bool) : valuationOf q 53 = true ∨ valuationOf q 799 = false ∨ valuationOf q 802 = true := by
  have hs : count800 q = (countLit q [-53]) + (countLit q [-56, -58]) := List.countP_append (p := literal q) (l₁ := [-53]) (l₂ := [-56, -58])
  have hm := merge_two (literal (valuationOf q) (-53)) (literal (valuationOf q) (799)) (literal (valuationOf q) (802)) (countLit q [-53]) (countLit q [-56, -58]) (count800 q) 1 2 (meaningNeg53 q) (meaning799 q) (meaning802 q) hs
  change (! (valuationOf q 53)) = false ∨ valuationOf q 799 = false ∨ valuationOf q 802 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause654 (q : Snake 81) (h : Conditions q) : valuation q 53 = true ∨ valuation q 799 = false ∨ valuation q 802 = true := counterClause654 (baseVal q)

theorem counterClause655 (q : Nat → Bool) : valuationOf q 64 = true ∨ valuationOf q 803 = true := by
  have hs : count803 q = (countLit q [-61]) + (countLit q [-64]) := List.countP_append (p := literal q) (l₁ := [-61]) (l₂ := [-64])
  have hm := merge_right (literal (valuationOf q) (-64)) (literal (valuationOf q) (803)) (countLit q [-61]) (countLit q [-64]) (count803 q) 1 (meaningNeg64 q) (meaning803 q) hs
  change (! (valuationOf q 64)) = false ∨ valuationOf q 803 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause655 (q : Snake 81) (h : Conditions q) : valuation q 64 = true ∨ valuation q 803 = true := counterClause655 (baseVal q)

theorem counterClause656 (q : Nat → Bool) : valuationOf q 61 = true ∨ valuationOf q 803 = true := by
  have hs : count803 q = (countLit q [-61]) + (countLit q [-64]) := List.countP_append (p := literal q) (l₁ := [-61]) (l₂ := [-64])
  have hm := merge_left (literal (valuationOf q) (-61)) (literal (valuationOf q) (803)) (countLit q [-61]) (countLit q [-64]) (count803 q) 1 (meaningNeg61 q) (meaning803 q) hs
  change (! (valuationOf q 61)) = false ∨ valuationOf q 803 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause656 (q : Snake 81) (h : Conditions q) : valuation q 61 = true ∨ valuation q 803 = true := counterClause656 (baseVal q)

theorem counterClause657 (q : Nat → Bool) : valuationOf q 61 = true ∨ valuationOf q 64 = true ∨ valuationOf q 804 = true := by
  have hs : count803 q = (countLit q [-61]) + (countLit q [-64]) := List.countP_append (p := literal q) (l₁ := [-61]) (l₂ := [-64])
  have hm := merge_two (literal (valuationOf q) (-61)) (literal (valuationOf q) (-64)) (literal (valuationOf q) (804)) (countLit q [-61]) (countLit q [-64]) (count803 q) 1 1 (meaningNeg61 q) (meaningNeg64 q) (meaning804 q) hs
  change (! (valuationOf q 61)) = false ∨ (! (valuationOf q 64)) = false ∨ valuationOf q 804 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause657 (q : Snake 81) (h : Conditions q) : valuation q 61 = true ∨ valuation q 64 = true ∨ valuation q 804 = true := counterClause657 (baseVal q)

theorem counterClause658 (q : Nat → Bool) : valuationOf q 803 = false ∨ valuationOf q 805 = true := by
  have hs : count805 q = (countLit q [-59]) + (countLit q [-61, -64]) := List.countP_append (p := literal q) (l₁ := [-59]) (l₂ := [-61, -64])
  have hm := merge_right (literal (valuationOf q) (803)) (literal (valuationOf q) (805)) (countLit q [-59]) (countLit q [-61, -64]) (count805 q) 1 (meaning803 q) (meaning805 q) hs
  change valuationOf q 803 = false ∨ valuationOf q 805 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause658 (q : Snake 81) (h : Conditions q) : valuation q 803 = false ∨ valuation q 805 = true := counterClause658 (baseVal q)

theorem counterClause659 (q : Nat → Bool) : valuationOf q 804 = false ∨ valuationOf q 806 = true := by
  have hs : count805 q = (countLit q [-59]) + (countLit q [-61, -64]) := List.countP_append (p := literal q) (l₁ := [-59]) (l₂ := [-61, -64])
  have hm := merge_right (literal (valuationOf q) (804)) (literal (valuationOf q) (806)) (countLit q [-59]) (countLit q [-61, -64]) (count805 q) 2 (meaning804 q) (meaning806 q) hs
  change valuationOf q 804 = false ∨ valuationOf q 806 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause659 (q : Snake 81) (h : Conditions q) : valuation q 804 = false ∨ valuation q 806 = true := counterClause659 (baseVal q)

theorem counterClause660 (q : Nat → Bool) : valuationOf q 59 = true ∨ valuationOf q 805 = true := by
  have hs : count805 q = (countLit q [-59]) + (countLit q [-61, -64]) := List.countP_append (p := literal q) (l₁ := [-59]) (l₂ := [-61, -64])
  have hm := merge_left (literal (valuationOf q) (-59)) (literal (valuationOf q) (805)) (countLit q [-59]) (countLit q [-61, -64]) (count805 q) 1 (meaningNeg59 q) (meaning805 q) hs
  change (! (valuationOf q 59)) = false ∨ valuationOf q 805 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause660 (q : Snake 81) (h : Conditions q) : valuation q 59 = true ∨ valuation q 805 = true := counterClause660 (baseVal q)

theorem counterClause661 (q : Nat → Bool) : valuationOf q 59 = true ∨ valuationOf q 803 = false ∨ valuationOf q 806 = true := by
  have hs : count805 q = (countLit q [-59]) + (countLit q [-61, -64]) := List.countP_append (p := literal q) (l₁ := [-59]) (l₂ := [-61, -64])
  have hm := merge_two (literal (valuationOf q) (-59)) (literal (valuationOf q) (803)) (literal (valuationOf q) (806)) (countLit q [-59]) (countLit q [-61, -64]) (count805 q) 1 1 (meaningNeg59 q) (meaning803 q) (meaning806 q) hs
  change (! (valuationOf q 59)) = false ∨ valuationOf q 803 = false ∨ valuationOf q 806 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause661 (q : Snake 81) (h : Conditions q) : valuation q 59 = true ∨ valuation q 803 = false ∨ valuation q 806 = true := counterClause661 (baseVal q)

theorem counterClause662 (q : Nat → Bool) : valuationOf q 59 = true ∨ valuationOf q 804 = false ∨ valuationOf q 807 = true := by
  have hs : count805 q = (countLit q [-59]) + (countLit q [-61, -64]) := List.countP_append (p := literal q) (l₁ := [-59]) (l₂ := [-61, -64])
  have hm := merge_two (literal (valuationOf q) (-59)) (literal (valuationOf q) (804)) (literal (valuationOf q) (807)) (countLit q [-59]) (countLit q [-61, -64]) (count805 q) 1 2 (meaningNeg59 q) (meaning804 q) (meaning807 q) hs
  change (! (valuationOf q 59)) = false ∨ valuationOf q 804 = false ∨ valuationOf q 807 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause662 (q : Snake 81) (h : Conditions q) : valuation q 59 = true ∨ valuation q 804 = false ∨ valuation q 807 = true := counterClause662 (baseVal q)

theorem counterClause663 (q : Nat → Bool) : valuationOf q 805 = false ∨ valuationOf q 808 = true := by
  have hs : count808 q = (countLit q [-53, -56, -58]) + (countLit q [-59, -61, -64]) := List.countP_append (p := literal q) (l₁ := [-53, -56, -58]) (l₂ := [-59, -61, -64])
  have hm := merge_right (literal (valuationOf q) (805)) (literal (valuationOf q) (808)) (countLit q [-53, -56, -58]) (countLit q [-59, -61, -64]) (count808 q) 1 (meaning805 q) (meaning808 q) hs
  change valuationOf q 805 = false ∨ valuationOf q 808 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause663 (q : Snake 81) (h : Conditions q) : valuation q 805 = false ∨ valuation q 808 = true := counterClause663 (baseVal q)

theorem counterClause664 (q : Nat → Bool) : valuationOf q 806 = false ∨ valuationOf q 809 = true := by
  have hs : count808 q = (countLit q [-53, -56, -58]) + (countLit q [-59, -61, -64]) := List.countP_append (p := literal q) (l₁ := [-53, -56, -58]) (l₂ := [-59, -61, -64])
  have hm := merge_right (literal (valuationOf q) (806)) (literal (valuationOf q) (809)) (countLit q [-53, -56, -58]) (countLit q [-59, -61, -64]) (count808 q) 2 (meaning806 q) (meaning809 q) hs
  change valuationOf q 806 = false ∨ valuationOf q 809 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause664 (q : Snake 81) (h : Conditions q) : valuation q 806 = false ∨ valuation q 809 = true := counterClause664 (baseVal q)

theorem counterClause665 (q : Nat → Bool) : valuationOf q 800 = false ∨ valuationOf q 808 = true := by
  have hs : count808 q = (countLit q [-53, -56, -58]) + (countLit q [-59, -61, -64]) := List.countP_append (p := literal q) (l₁ := [-53, -56, -58]) (l₂ := [-59, -61, -64])
  have hm := merge_left (literal (valuationOf q) (800)) (literal (valuationOf q) (808)) (countLit q [-53, -56, -58]) (countLit q [-59, -61, -64]) (count808 q) 1 (meaning800 q) (meaning808 q) hs
  change valuationOf q 800 = false ∨ valuationOf q 808 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause665 (q : Snake 81) (h : Conditions q) : valuation q 800 = false ∨ valuation q 808 = true := counterClause665 (baseVal q)

theorem counterClause666 (q : Nat → Bool) : valuationOf q 800 = false ∨ valuationOf q 805 = false ∨ valuationOf q 809 = true := by
  have hs : count808 q = (countLit q [-53, -56, -58]) + (countLit q [-59, -61, -64]) := List.countP_append (p := literal q) (l₁ := [-53, -56, -58]) (l₂ := [-59, -61, -64])
  have hm := merge_two (literal (valuationOf q) (800)) (literal (valuationOf q) (805)) (literal (valuationOf q) (809)) (countLit q [-53, -56, -58]) (countLit q [-59, -61, -64]) (count808 q) 1 1 (meaning800 q) (meaning805 q) (meaning809 q) hs
  change valuationOf q 800 = false ∨ valuationOf q 805 = false ∨ valuationOf q 809 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause666 (q : Snake 81) (h : Conditions q) : valuation q 800 = false ∨ valuation q 805 = false ∨ valuation q 809 = true := counterClause666 (baseVal q)

theorem counterClause667 (q : Nat → Bool) : valuationOf q 800 = false ∨ valuationOf q 807 = false ∨ valuationOf q 811 = true := by
  have hs : count808 q = (countLit q [-53, -56, -58]) + (countLit q [-59, -61, -64]) := List.countP_append (p := literal q) (l₁ := [-53, -56, -58]) (l₂ := [-59, -61, -64])
  have hm := merge_two (literal (valuationOf q) (800)) (literal (valuationOf q) (807)) (literal (valuationOf q) (811)) (countLit q [-53, -56, -58]) (countLit q [-59, -61, -64]) (count808 q) 1 3 (meaning800 q) (meaning807 q) (meaning811 q) hs
  change valuationOf q 800 = false ∨ valuationOf q 807 = false ∨ valuationOf q 811 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause667 (q : Snake 81) (h : Conditions q) : valuation q 800 = false ∨ valuation q 807 = false ∨ valuation q 811 = true := counterClause667 (baseVal q)

theorem counterClause668 (q : Nat → Bool) : valuationOf q 801 = false ∨ valuationOf q 809 = true := by
  have hs : count808 q = (countLit q [-53, -56, -58]) + (countLit q [-59, -61, -64]) := List.countP_append (p := literal q) (l₁ := [-53, -56, -58]) (l₂ := [-59, -61, -64])
  have hm := merge_left (literal (valuationOf q) (801)) (literal (valuationOf q) (809)) (countLit q [-53, -56, -58]) (countLit q [-59, -61, -64]) (count808 q) 2 (meaning801 q) (meaning809 q) hs
  change valuationOf q 801 = false ∨ valuationOf q 809 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause668 (q : Snake 81) (h : Conditions q) : valuation q 801 = false ∨ valuation q 809 = true := counterClause668 (baseVal q)

theorem counterClause669 (q : Nat → Bool) : valuationOf q 801 = false ∨ valuationOf q 805 = false ∨ valuationOf q 810 = true := by
  have hs : count808 q = (countLit q [-53, -56, -58]) + (countLit q [-59, -61, -64]) := List.countP_append (p := literal q) (l₁ := [-53, -56, -58]) (l₂ := [-59, -61, -64])
  have hm := merge_two (literal (valuationOf q) (801)) (literal (valuationOf q) (805)) (literal (valuationOf q) (810)) (countLit q [-53, -56, -58]) (countLit q [-59, -61, -64]) (count808 q) 2 1 (meaning801 q) (meaning805 q) (meaning810 q) hs
  change valuationOf q 801 = false ∨ valuationOf q 805 = false ∨ valuationOf q 810 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause669 (q : Snake 81) (h : Conditions q) : valuation q 801 = false ∨ valuation q 805 = false ∨ valuation q 810 = true := counterClause669 (baseVal q)

theorem counterClause670 (q : Nat → Bool) : valuationOf q 801 = false ∨ valuationOf q 806 = false ∨ valuationOf q 811 = true := by
  have hs : count808 q = (countLit q [-53, -56, -58]) + (countLit q [-59, -61, -64]) := List.countP_append (p := literal q) (l₁ := [-53, -56, -58]) (l₂ := [-59, -61, -64])
  have hm := merge_two (literal (valuationOf q) (801)) (literal (valuationOf q) (806)) (literal (valuationOf q) (811)) (countLit q [-53, -56, -58]) (countLit q [-59, -61, -64]) (count808 q) 2 2 (meaning801 q) (meaning806 q) (meaning811 q) hs
  change valuationOf q 801 = false ∨ valuationOf q 806 = false ∨ valuationOf q 811 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause670 (q : Snake 81) (h : Conditions q) : valuation q 801 = false ∨ valuation q 806 = false ∨ valuation q 811 = true := counterClause670 (baseVal q)

theorem counterClause671 (q : Nat → Bool) : valuationOf q 802 = false ∨ valuationOf q 805 = false ∨ valuationOf q 811 = true := by
  have hs : count808 q = (countLit q [-53, -56, -58]) + (countLit q [-59, -61, -64]) := List.countP_append (p := literal q) (l₁ := [-53, -56, -58]) (l₂ := [-59, -61, -64])
  have hm := merge_two (literal (valuationOf q) (802)) (literal (valuationOf q) (805)) (literal (valuationOf q) (811)) (countLit q [-53, -56, -58]) (countLit q [-59, -61, -64]) (count808 q) 3 1 (meaning802 q) (meaning805 q) (meaning811 q) hs
  change valuationOf q 802 = false ∨ valuationOf q 805 = false ∨ valuationOf q 811 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause671 (q : Snake 81) (h : Conditions q) : valuation q 802 = false ∨ valuation q 805 = false ∨ valuation q 811 = true := counterClause671 (baseVal q)

theorem counterClause672 (q : Nat → Bool) : valuationOf q 802 = false ∨ valuationOf q 806 = false ∨ valuationOf q 812 = true := by
  have hs : count808 q = (countLit q [-53, -56, -58]) + (countLit q [-59, -61, -64]) := List.countP_append (p := literal q) (l₁ := [-53, -56, -58]) (l₂ := [-59, -61, -64])
  have hm := merge_two (literal (valuationOf q) (802)) (literal (valuationOf q) (806)) (literal (valuationOf q) (812)) (countLit q [-53, -56, -58]) (countLit q [-59, -61, -64]) (count808 q) 3 2 (meaning802 q) (meaning806 q) (meaning812 q) hs
  change valuationOf q 802 = false ∨ valuationOf q 806 = false ∨ valuationOf q 812 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause672 (q : Snake 81) (h : Conditions q) : valuation q 802 = false ∨ valuation q 806 = false ∨ valuation q 812 = true := counterClause672 (baseVal q)

theorem block20 (q : Snake 81) (h : Conditions q) : B112E174.Block20 (valuation q) :=
  ⟨clause641 q h, clause642 q h, clause643 q h, clause644 q h, clause645 q h, clause646 q h, clause647 q h, clause648 q h, clause649 q h, clause650 q h, clause651 q h, clause652 q h, clause653 q h, clause654 q h, clause655 q h, clause656 q h, clause657 q h, clause658 q h, clause659 q h, clause660 q h, clause661 q h, clause662 q h, clause663 q h, clause664 q h, clause665 q h, clause666 q h, clause667 q h, clause668 q h, clause669 q h, clause670 q h, clause671 q h, clause672 q h⟩

end
end Snake9.Regrowth.E112174
