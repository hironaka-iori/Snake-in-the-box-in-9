import E112151Semantics
import B112E151Inputs
namespace Snake9.Regrowth.E112151
noncomputable section
local instance blockDec11 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause353 (q : Nat → Bool) : valuationOf q 746 = false ∨ valuationOf q 757 = true := by
  have hs : count756 q = (countLit q [-13, -14, -17]) + (countLit q [-20, -22, -24, -25]) := List.countP_append (p := literal q) (l₁ := [-13, -14, -17]) (l₂ := [-20, -22, -24, -25])
  have hm := merge_left (literal (valuationOf q) (746)) (literal (valuationOf q) (757)) (countLit q [-13, -14, -17]) (countLit q [-20, -22, -24, -25]) (count756 q) 2 (meaning746 q) (meaning757 q) hs
  change valuationOf q 746 = false ∨ valuationOf q 757 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause353 (q : Snake 81) (h : Conditions q) : valuation q 746 = false ∨ valuation q 757 = true := counterClause353 (baseVal q)

theorem counterClause354 (q : Nat → Bool) : valuationOf q 746 = false ∨ valuationOf q 753 = false ∨ valuationOf q 759 = true := by
  have hs : count756 q = (countLit q [-13, -14, -17]) + (countLit q [-20, -22, -24, -25]) := List.countP_append (p := literal q) (l₁ := [-13, -14, -17]) (l₂ := [-20, -22, -24, -25])
  have hm := merge_two (literal (valuationOf q) (746)) (literal (valuationOf q) (753)) (literal (valuationOf q) (759)) (countLit q [-13, -14, -17]) (countLit q [-20, -22, -24, -25]) (count756 q) 2 2 (meaning746 q) (meaning753 q) (meaning759 q) hs
  change valuationOf q 746 = false ∨ valuationOf q 753 = false ∨ valuationOf q 759 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause354 (q : Snake 81) (h : Conditions q) : valuation q 746 = false ∨ valuation q 753 = false ∨ valuation q 759 = true := counterClause354 (baseVal q)

theorem counterClause355 (q : Nat → Bool) : valuationOf q 737 = false ∨ valuationOf q 756 = false ∨ valuationOf q 764 = true := by
  have hs : count763 q = (countLit q [-1, -3, -5, -7, -9, -10]) + (countLit q [-13, -14, -17, -20, -22, -24, -25]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -5, -7, -9, -10]) (l₂ := [-13, -14, -17, -20, -22, -24, -25])
  have hm := merge_two (literal (valuationOf q) (737)) (literal (valuationOf q) (756)) (literal (valuationOf q) (764)) (countLit q [-1, -3, -5, -7, -9, -10]) (countLit q [-13, -14, -17, -20, -22, -24, -25]) (count763 q) 1 1 (meaning737 q) (meaning756 q) (meaning764 q) hs
  change valuationOf q 737 = false ∨ valuationOf q 756 = false ∨ valuationOf q 764 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause355 (q : Snake 81) (h : Conditions q) : valuation q 737 = false ∨ valuation q 756 = false ∨ valuation q 764 = true := counterClause355 (baseVal q)

theorem counterClause356 (q : Nat → Bool) : valuationOf q 737 = false ∨ valuationOf q 757 = false ∨ valuationOf q 765 = true := by
  have hs : count763 q = (countLit q [-1, -3, -5, -7, -9, -10]) + (countLit q [-13, -14, -17, -20, -22, -24, -25]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -5, -7, -9, -10]) (l₂ := [-13, -14, -17, -20, -22, -24, -25])
  have hm := merge_two (literal (valuationOf q) (737)) (literal (valuationOf q) (757)) (literal (valuationOf q) (765)) (countLit q [-1, -3, -5, -7, -9, -10]) (countLit q [-13, -14, -17, -20, -22, -24, -25]) (count763 q) 1 2 (meaning737 q) (meaning757 q) (meaning765 q) hs
  change valuationOf q 737 = false ∨ valuationOf q 757 = false ∨ valuationOf q 765 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause356 (q : Snake 81) (h : Conditions q) : valuation q 737 = false ∨ valuation q 757 = false ∨ valuation q 765 = true := counterClause356 (baseVal q)

theorem counterClause357 (q : Nat → Bool) : valuationOf q 737 = false ∨ valuationOf q 758 = false ∨ valuationOf q 766 = true := by
  have hs : count763 q = (countLit q [-1, -3, -5, -7, -9, -10]) + (countLit q [-13, -14, -17, -20, -22, -24, -25]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -5, -7, -9, -10]) (l₂ := [-13, -14, -17, -20, -22, -24, -25])
  have hm := merge_two (literal (valuationOf q) (737)) (literal (valuationOf q) (758)) (literal (valuationOf q) (766)) (countLit q [-1, -3, -5, -7, -9, -10]) (countLit q [-13, -14, -17, -20, -22, -24, -25]) (count763 q) 1 3 (meaning737 q) (meaning758 q) (meaning766 q) hs
  change valuationOf q 737 = false ∨ valuationOf q 758 = false ∨ valuationOf q 766 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause357 (q : Snake 81) (h : Conditions q) : valuation q 737 = false ∨ valuation q 758 = false ∨ valuation q 766 = true := counterClause357 (baseVal q)

theorem counterClause358 (q : Nat → Bool) : valuationOf q 737 = false ∨ valuationOf q 759 = false ∨ valuationOf q 767 = true := by
  have hs : count763 q = (countLit q [-1, -3, -5, -7, -9, -10]) + (countLit q [-13, -14, -17, -20, -22, -24, -25]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -5, -7, -9, -10]) (l₂ := [-13, -14, -17, -20, -22, -24, -25])
  have hm := merge_two (literal (valuationOf q) (737)) (literal (valuationOf q) (759)) (literal (valuationOf q) (767)) (countLit q [-1, -3, -5, -7, -9, -10]) (countLit q [-13, -14, -17, -20, -22, -24, -25]) (count763 q) 1 4 (meaning737 q) (meaning759 q) (meaning767 q) hs
  change valuationOf q 737 = false ∨ valuationOf q 759 = false ∨ valuationOf q 767 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause358 (q : Snake 81) (h : Conditions q) : valuation q 737 = false ∨ valuation q 759 = false ∨ valuation q 767 = true := counterClause358 (baseVal q)

theorem counterClause359 (q : Nat → Bool) : valuationOf q 738 = false ∨ valuationOf q 756 = false ∨ valuationOf q 765 = true := by
  have hs : count763 q = (countLit q [-1, -3, -5, -7, -9, -10]) + (countLit q [-13, -14, -17, -20, -22, -24, -25]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -5, -7, -9, -10]) (l₂ := [-13, -14, -17, -20, -22, -24, -25])
  have hm := merge_two (literal (valuationOf q) (738)) (literal (valuationOf q) (756)) (literal (valuationOf q) (765)) (countLit q [-1, -3, -5, -7, -9, -10]) (countLit q [-13, -14, -17, -20, -22, -24, -25]) (count763 q) 2 1 (meaning738 q) (meaning756 q) (meaning765 q) hs
  change valuationOf q 738 = false ∨ valuationOf q 756 = false ∨ valuationOf q 765 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause359 (q : Snake 81) (h : Conditions q) : valuation q 738 = false ∨ valuation q 756 = false ∨ valuation q 765 = true := counterClause359 (baseVal q)

theorem counterClause360 (q : Nat → Bool) : valuationOf q 738 = false ∨ valuationOf q 757 = false ∨ valuationOf q 766 = true := by
  have hs : count763 q = (countLit q [-1, -3, -5, -7, -9, -10]) + (countLit q [-13, -14, -17, -20, -22, -24, -25]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -5, -7, -9, -10]) (l₂ := [-13, -14, -17, -20, -22, -24, -25])
  have hm := merge_two (literal (valuationOf q) (738)) (literal (valuationOf q) (757)) (literal (valuationOf q) (766)) (countLit q [-1, -3, -5, -7, -9, -10]) (countLit q [-13, -14, -17, -20, -22, -24, -25]) (count763 q) 2 2 (meaning738 q) (meaning757 q) (meaning766 q) hs
  change valuationOf q 738 = false ∨ valuationOf q 757 = false ∨ valuationOf q 766 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause360 (q : Snake 81) (h : Conditions q) : valuation q 738 = false ∨ valuation q 757 = false ∨ valuation q 766 = true := counterClause360 (baseVal q)

theorem counterClause361 (q : Nat → Bool) : valuationOf q 739 = false ∨ valuationOf q 756 = false ∨ valuationOf q 766 = true := by
  have hs : count763 q = (countLit q [-1, -3, -5, -7, -9, -10]) + (countLit q [-13, -14, -17, -20, -22, -24, -25]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -5, -7, -9, -10]) (l₂ := [-13, -14, -17, -20, -22, -24, -25])
  have hm := merge_two (literal (valuationOf q) (739)) (literal (valuationOf q) (756)) (literal (valuationOf q) (766)) (countLit q [-1, -3, -5, -7, -9, -10]) (countLit q [-13, -14, -17, -20, -22, -24, -25]) (count763 q) 3 1 (meaning739 q) (meaning756 q) (meaning766 q) hs
  change valuationOf q 739 = false ∨ valuationOf q 756 = false ∨ valuationOf q 766 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause361 (q : Snake 81) (h : Conditions q) : valuation q 739 = false ∨ valuation q 756 = false ∨ valuation q 766 = true := counterClause361 (baseVal q)

theorem counterClause362 (q : Nat → Bool) : valuationOf q 30 = true ∨ valuationOf q 776 = true := by
  have hs : count776 q = (countLit q [-29]) + (countLit q [-30]) := List.countP_append (p := literal q) (l₁ := [-29]) (l₂ := [-30])
  have hm := merge_right (literal (valuationOf q) (-30)) (literal (valuationOf q) (776)) (countLit q [-29]) (countLit q [-30]) (count776 q) 1 (meaningNeg30 q) (meaning776 q) hs
  change (! (valuationOf q 30)) = false ∨ valuationOf q 776 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause362 (q : Snake 81) (h : Conditions q) : valuation q 30 = true ∨ valuation q 776 = true := counterClause362 (baseVal q)

theorem counterClause363 (q : Nat → Bool) : valuationOf q 29 = true ∨ valuationOf q 776 = true := by
  have hs : count776 q = (countLit q [-29]) + (countLit q [-30]) := List.countP_append (p := literal q) (l₁ := [-29]) (l₂ := [-30])
  have hm := merge_left (literal (valuationOf q) (-29)) (literal (valuationOf q) (776)) (countLit q [-29]) (countLit q [-30]) (count776 q) 1 (meaningNeg29 q) (meaning776 q) hs
  change (! (valuationOf q 29)) = false ∨ valuationOf q 776 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause363 (q : Snake 81) (h : Conditions q) : valuation q 29 = true ∨ valuation q 776 = true := counterClause363 (baseVal q)

theorem counterClause364 (q : Nat → Bool) : valuationOf q 776 = false ∨ valuationOf q 778 = true := by
  have hs : count778 q = (countLit q [-28]) + (countLit q [-29, -30]) := List.countP_append (p := literal q) (l₁ := [-28]) (l₂ := [-29, -30])
  have hm := merge_right (literal (valuationOf q) (776)) (literal (valuationOf q) (778)) (countLit q [-28]) (countLit q [-29, -30]) (count778 q) 1 (meaning776 q) (meaning778 q) hs
  change valuationOf q 776 = false ∨ valuationOf q 778 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause364 (q : Snake 81) (h : Conditions q) : valuation q 776 = false ∨ valuation q 778 = true := counterClause364 (baseVal q)

theorem counterClause365 (q : Nat → Bool) : valuationOf q 28 = true ∨ valuationOf q 778 = true := by
  have hs : count778 q = (countLit q [-28]) + (countLit q [-29, -30]) := List.countP_append (p := literal q) (l₁ := [-28]) (l₂ := [-29, -30])
  have hm := merge_left (literal (valuationOf q) (-28)) (literal (valuationOf q) (778)) (countLit q [-28]) (countLit q [-29, -30]) (count778 q) 1 (meaningNeg28 q) (meaning778 q) hs
  change (! (valuationOf q 28)) = false ∨ valuationOf q 778 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause365 (q : Snake 81) (h : Conditions q) : valuation q 28 = true ∨ valuation q 778 = true := counterClause365 (baseVal q)

theorem counterClause366 (q : Nat → Bool) : valuationOf q 28 = true ∨ valuationOf q 776 = false ∨ valuationOf q 779 = true := by
  have hs : count778 q = (countLit q [-28]) + (countLit q [-29, -30]) := List.countP_append (p := literal q) (l₁ := [-28]) (l₂ := [-29, -30])
  have hm := merge_two (literal (valuationOf q) (-28)) (literal (valuationOf q) (776)) (literal (valuationOf q) (779)) (countLit q [-28]) (countLit q [-29, -30]) (count778 q) 1 1 (meaningNeg28 q) (meaning776 q) (meaning779 q) hs
  change (! (valuationOf q 28)) = false ∨ valuationOf q 776 = false ∨ valuationOf q 779 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause366 (q : Snake 81) (h : Conditions q) : valuation q 28 = true ∨ valuation q 776 = false ∨ valuation q 779 = true := counterClause366 (baseVal q)

theorem counterClause367 (q : Nat → Bool) : valuationOf q 33 = true ∨ valuationOf q 781 = true := by
  have hs : count781 q = (countLit q [-33]) + (countLit q [-36]) := List.countP_append (p := literal q) (l₁ := [-33]) (l₂ := [-36])
  have hm := merge_left (literal (valuationOf q) (-33)) (literal (valuationOf q) (781)) (countLit q [-33]) (countLit q [-36]) (count781 q) 1 (meaningNeg33 q) (meaning781 q) hs
  change (! (valuationOf q 33)) = false ∨ valuationOf q 781 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause367 (q : Snake 81) (h : Conditions q) : valuation q 33 = true ∨ valuation q 781 = true := counterClause367 (baseVal q)

theorem counterClause368 (q : Nat → Bool) : valuationOf q 40 = true ∨ valuationOf q 783 = true := by
  have hs : count783 q = (countLit q [-38]) + (countLit q [-40]) := List.countP_append (p := literal q) (l₁ := [-38]) (l₂ := [-40])
  have hm := merge_right (literal (valuationOf q) (-40)) (literal (valuationOf q) (783)) (countLit q [-38]) (countLit q [-40]) (count783 q) 1 (meaningNeg40 q) (meaning783 q) hs
  change (! (valuationOf q 40)) = false ∨ valuationOf q 783 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause368 (q : Snake 81) (h : Conditions q) : valuation q 40 = true ∨ valuation q 783 = true := counterClause368 (baseVal q)

theorem counterClause369 (q : Nat → Bool) : valuationOf q 38 = true ∨ valuationOf q 783 = true := by
  have hs : count783 q = (countLit q [-38]) + (countLit q [-40]) := List.countP_append (p := literal q) (l₁ := [-38]) (l₂ := [-40])
  have hm := merge_left (literal (valuationOf q) (-38)) (literal (valuationOf q) (783)) (countLit q [-38]) (countLit q [-40]) (count783 q) 1 (meaningNeg38 q) (meaning783 q) hs
  change (! (valuationOf q 38)) = false ∨ valuationOf q 783 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause369 (q : Snake 81) (h : Conditions q) : valuation q 38 = true ∨ valuation q 783 = true := counterClause369 (baseVal q)

theorem counterClause370 (q : Nat → Bool) : valuationOf q 783 = false ∨ valuationOf q 785 = true := by
  have hs : count785 q = (countLit q [-33, -36]) + (countLit q [-38, -40]) := List.countP_append (p := literal q) (l₁ := [-33, -36]) (l₂ := [-38, -40])
  have hm := merge_right (literal (valuationOf q) (783)) (literal (valuationOf q) (785)) (countLit q [-33, -36]) (countLit q [-38, -40]) (count785 q) 1 (meaning783 q) (meaning785 q) hs
  change valuationOf q 783 = false ∨ valuationOf q 785 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause370 (q : Snake 81) (h : Conditions q) : valuation q 783 = false ∨ valuation q 785 = true := counterClause370 (baseVal q)

theorem counterClause371 (q : Nat → Bool) : valuationOf q 781 = false ∨ valuationOf q 785 = true := by
  have hs : count785 q = (countLit q [-33, -36]) + (countLit q [-38, -40]) := List.countP_append (p := literal q) (l₁ := [-33, -36]) (l₂ := [-38, -40])
  have hm := merge_left (literal (valuationOf q) (781)) (literal (valuationOf q) (785)) (countLit q [-33, -36]) (countLit q [-38, -40]) (count785 q) 1 (meaning781 q) (meaning785 q) hs
  change valuationOf q 781 = false ∨ valuationOf q 785 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause371 (q : Snake 81) (h : Conditions q) : valuation q 781 = false ∨ valuation q 785 = true := counterClause371 (baseVal q)

theorem counterClause372 (q : Nat → Bool) : valuationOf q 781 = false ∨ valuationOf q 783 = false ∨ valuationOf q 786 = true := by
  have hs : count785 q = (countLit q [-33, -36]) + (countLit q [-38, -40]) := List.countP_append (p := literal q) (l₁ := [-33, -36]) (l₂ := [-38, -40])
  have hm := merge_two (literal (valuationOf q) (781)) (literal (valuationOf q) (783)) (literal (valuationOf q) (786)) (countLit q [-33, -36]) (countLit q [-38, -40]) (count785 q) 1 1 (meaning781 q) (meaning783 q) (meaning786 q) hs
  change valuationOf q 781 = false ∨ valuationOf q 783 = false ∨ valuationOf q 786 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause372 (q : Snake 81) (h : Conditions q) : valuation q 781 = false ∨ valuation q 783 = false ∨ valuation q 786 = true := counterClause372 (baseVal q)

theorem counterClause373 (q : Nat → Bool) : valuationOf q 785 = false ∨ valuationOf q 789 = true := by
  have hs : count789 q = (countLit q [-28, -29, -30]) + (countLit q [-33, -36, -38, -40]) := List.countP_append (p := literal q) (l₁ := [-28, -29, -30]) (l₂ := [-33, -36, -38, -40])
  have hm := merge_right (literal (valuationOf q) (785)) (literal (valuationOf q) (789)) (countLit q [-28, -29, -30]) (countLit q [-33, -36, -38, -40]) (count789 q) 1 (meaning785 q) (meaning789 q) hs
  change valuationOf q 785 = false ∨ valuationOf q 789 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause373 (q : Snake 81) (h : Conditions q) : valuation q 785 = false ∨ valuation q 789 = true := counterClause373 (baseVal q)

theorem counterClause374 (q : Nat → Bool) : valuationOf q 786 = false ∨ valuationOf q 790 = true := by
  have hs : count789 q = (countLit q [-28, -29, -30]) + (countLit q [-33, -36, -38, -40]) := List.countP_append (p := literal q) (l₁ := [-28, -29, -30]) (l₂ := [-33, -36, -38, -40])
  have hm := merge_right (literal (valuationOf q) (786)) (literal (valuationOf q) (790)) (countLit q [-28, -29, -30]) (countLit q [-33, -36, -38, -40]) (count789 q) 2 (meaning786 q) (meaning790 q) hs
  change valuationOf q 786 = false ∨ valuationOf q 790 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause374 (q : Snake 81) (h : Conditions q) : valuation q 786 = false ∨ valuation q 790 = true := counterClause374 (baseVal q)

theorem counterClause375 (q : Nat → Bool) : valuationOf q 778 = false ∨ valuationOf q 785 = false ∨ valuationOf q 790 = true := by
  have hs : count789 q = (countLit q [-28, -29, -30]) + (countLit q [-33, -36, -38, -40]) := List.countP_append (p := literal q) (l₁ := [-28, -29, -30]) (l₂ := [-33, -36, -38, -40])
  have hm := merge_two (literal (valuationOf q) (778)) (literal (valuationOf q) (785)) (literal (valuationOf q) (790)) (countLit q [-28, -29, -30]) (countLit q [-33, -36, -38, -40]) (count789 q) 1 1 (meaning778 q) (meaning785 q) (meaning790 q) hs
  change valuationOf q 778 = false ∨ valuationOf q 785 = false ∨ valuationOf q 790 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause375 (q : Snake 81) (h : Conditions q) : valuation q 778 = false ∨ valuation q 785 = false ∨ valuation q 790 = true := counterClause375 (baseVal q)

theorem counterClause376 (q : Nat → Bool) : valuationOf q 778 = false ∨ valuationOf q 786 = false ∨ valuationOf q 791 = true := by
  have hs : count789 q = (countLit q [-28, -29, -30]) + (countLit q [-33, -36, -38, -40]) := List.countP_append (p := literal q) (l₁ := [-28, -29, -30]) (l₂ := [-33, -36, -38, -40])
  have hm := merge_two (literal (valuationOf q) (778)) (literal (valuationOf q) (786)) (literal (valuationOf q) (791)) (countLit q [-28, -29, -30]) (countLit q [-33, -36, -38, -40]) (count789 q) 1 2 (meaning778 q) (meaning786 q) (meaning791 q) hs
  change valuationOf q 778 = false ∨ valuationOf q 786 = false ∨ valuationOf q 791 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause376 (q : Snake 81) (h : Conditions q) : valuation q 778 = false ∨ valuation q 786 = false ∨ valuation q 791 = true := counterClause376 (baseVal q)

theorem counterClause377 (q : Nat → Bool) : valuationOf q 779 = false ∨ valuationOf q 785 = false ∨ valuationOf q 791 = true := by
  have hs : count789 q = (countLit q [-28, -29, -30]) + (countLit q [-33, -36, -38, -40]) := List.countP_append (p := literal q) (l₁ := [-28, -29, -30]) (l₂ := [-33, -36, -38, -40])
  have hm := merge_two (literal (valuationOf q) (779)) (literal (valuationOf q) (785)) (literal (valuationOf q) (791)) (countLit q [-28, -29, -30]) (countLit q [-33, -36, -38, -40]) (count789 q) 2 1 (meaning779 q) (meaning785 q) (meaning791 q) hs
  change valuationOf q 779 = false ∨ valuationOf q 785 = false ∨ valuationOf q 791 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause377 (q : Snake 81) (h : Conditions q) : valuation q 779 = false ∨ valuation q 785 = false ∨ valuation q 791 = true := counterClause377 (baseVal q)

theorem counterClause378 (q : Nat → Bool) : valuationOf q 45 = true ∨ valuationOf q 796 = true := by
  have hs : count796 q = (countLit q [-42]) + (countLit q [-45]) := List.countP_append (p := literal q) (l₁ := [-42]) (l₂ := [-45])
  have hm := merge_right (literal (valuationOf q) (-45)) (literal (valuationOf q) (796)) (countLit q [-42]) (countLit q [-45]) (count796 q) 1 (meaningNeg45 q) (meaning796 q) hs
  change (! (valuationOf q 45)) = false ∨ valuationOf q 796 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause378 (q : Snake 81) (h : Conditions q) : valuation q 45 = true ∨ valuation q 796 = true := counterClause378 (baseVal q)

theorem counterClause379 (q : Nat → Bool) : valuationOf q 42 = true ∨ valuationOf q 796 = true := by
  have hs : count796 q = (countLit q [-42]) + (countLit q [-45]) := List.countP_append (p := literal q) (l₁ := [-42]) (l₂ := [-45])
  have hm := merge_left (literal (valuationOf q) (-42)) (literal (valuationOf q) (796)) (countLit q [-42]) (countLit q [-45]) (count796 q) 1 (meaningNeg42 q) (meaning796 q) hs
  change (! (valuationOf q 42)) = false ∨ valuationOf q 796 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause379 (q : Snake 81) (h : Conditions q) : valuation q 42 = true ∨ valuation q 796 = true := counterClause379 (baseVal q)

theorem counterClause380 (q : Nat → Bool) : valuationOf q 42 = true ∨ valuationOf q 45 = true ∨ valuationOf q 797 = true := by
  have hs : count796 q = (countLit q [-42]) + (countLit q [-45]) := List.countP_append (p := literal q) (l₁ := [-42]) (l₂ := [-45])
  have hm := merge_two (literal (valuationOf q) (-42)) (literal (valuationOf q) (-45)) (literal (valuationOf q) (797)) (countLit q [-42]) (countLit q [-45]) (count796 q) 1 1 (meaningNeg42 q) (meaningNeg45 q) (meaning797 q) hs
  change (! (valuationOf q 42)) = false ∨ (! (valuationOf q 45)) = false ∨ valuationOf q 797 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause380 (q : Snake 81) (h : Conditions q) : valuation q 42 = true ∨ valuation q 45 = true ∨ valuation q 797 = true := counterClause380 (baseVal q)

theorem counterClause381 (q : Nat → Bool) : valuationOf q 796 = false ∨ valuationOf q 798 = true := by
  have hs : count798 q = (countLit q [-41]) + (countLit q [-42, -45]) := List.countP_append (p := literal q) (l₁ := [-41]) (l₂ := [-42, -45])
  have hm := merge_right (literal (valuationOf q) (796)) (literal (valuationOf q) (798)) (countLit q [-41]) (countLit q [-42, -45]) (count798 q) 1 (meaning796 q) (meaning798 q) hs
  change valuationOf q 796 = false ∨ valuationOf q 798 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause381 (q : Snake 81) (h : Conditions q) : valuation q 796 = false ∨ valuation q 798 = true := counterClause381 (baseVal q)

theorem counterClause382 (q : Nat → Bool) : valuationOf q 797 = false ∨ valuationOf q 799 = true := by
  have hs : count798 q = (countLit q [-41]) + (countLit q [-42, -45]) := List.countP_append (p := literal q) (l₁ := [-41]) (l₂ := [-42, -45])
  have hm := merge_right (literal (valuationOf q) (797)) (literal (valuationOf q) (799)) (countLit q [-41]) (countLit q [-42, -45]) (count798 q) 2 (meaning797 q) (meaning799 q) hs
  change valuationOf q 797 = false ∨ valuationOf q 799 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause382 (q : Snake 81) (h : Conditions q) : valuation q 797 = false ∨ valuation q 799 = true := counterClause382 (baseVal q)

theorem counterClause383 (q : Nat → Bool) : valuationOf q 41 = true ∨ valuationOf q 798 = true := by
  have hs : count798 q = (countLit q [-41]) + (countLit q [-42, -45]) := List.countP_append (p := literal q) (l₁ := [-41]) (l₂ := [-42, -45])
  have hm := merge_left (literal (valuationOf q) (-41)) (literal (valuationOf q) (798)) (countLit q [-41]) (countLit q [-42, -45]) (count798 q) 1 (meaningNeg41 q) (meaning798 q) hs
  change (! (valuationOf q 41)) = false ∨ valuationOf q 798 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause383 (q : Snake 81) (h : Conditions q) : valuation q 41 = true ∨ valuation q 798 = true := counterClause383 (baseVal q)

theorem counterClause384 (q : Nat → Bool) : valuationOf q 49 = true ∨ valuationOf q 801 = true := by
  have hs : count801 q = (countLit q [-46]) + (countLit q [-49]) := List.countP_append (p := literal q) (l₁ := [-46]) (l₂ := [-49])
  have hm := merge_right (literal (valuationOf q) (-49)) (literal (valuationOf q) (801)) (countLit q [-46]) (countLit q [-49]) (count801 q) 1 (meaningNeg49 q) (meaning801 q) hs
  change (! (valuationOf q 49)) = false ∨ valuationOf q 801 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause384 (q : Snake 81) (h : Conditions q) : valuation q 49 = true ∨ valuation q 801 = true := counterClause384 (baseVal q)

theorem block11 (q : Snake 81) (h : Conditions q) : B112E151.Block11 (valuation q) :=
  ⟨clause353 q h, clause354 q h, clause355 q h, clause356 q h, clause357 q h, clause358 q h, clause359 q h, clause360 q h, clause361 q h, clause362 q h, clause363 q h, clause364 q h, clause365 q h, clause366 q h, clause367 q h, clause368 q h, clause369 q h, clause370 q h, clause371 q h, clause372 q h, clause373 q h, clause374 q h, clause375 q h, clause376 q h, clause377 q h, clause378 q h, clause379 q h, clause380 q h, clause381 q h, clause382 q h, clause383 q h, clause384 q h⟩

end
end Snake9.Regrowth.E112151
