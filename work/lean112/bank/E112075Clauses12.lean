import E112075Semantics
import B112E075Inputs
namespace Snake9.Regrowth.E112075
noncomputable section
local instance blockDec12 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause385 (q : Nat → Bool) : valuationOf q 748 = false ∨ valuationOf q 766 = false ∨ valuationOf q 775 = true := by
  have hs : count773 q = (countLit q [-28, -29, -30, -33, -37, -39]) + (countLit q [-40, -43, -44, -45, -47, -50, -52]) := List.countP_append (p := literal q) (l₁ := [-28, -29, -30, -33, -37, -39]) (l₂ := [-40, -43, -44, -45, -47, -50, -52])
  have hm := merge_two (literal (valuationOf q) (748)) (literal (valuationOf q) (766)) (literal (valuationOf q) (775)) (countLit q [-28, -29, -30, -33, -37, -39]) (countLit q [-40, -43, -44, -45, -47, -50, -52]) (count773 q) 2 1 (meaning748 q) (meaning766 q) (meaning775 q) hs
  change valuationOf q 748 = false ∨ valuationOf q 766 = false ∨ valuationOf q 775 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause385 (q : Snake 81) (h : Conditions q) : valuation q 748 = false ∨ valuation q 766 = false ∨ valuation q 775 = true := counterClause385 (baseVal q)

theorem counterClause386 (q : Nat → Bool) : valuationOf q 748 = false ∨ valuationOf q 767 = false ∨ valuationOf q 776 = true := by
  have hs : count773 q = (countLit q [-28, -29, -30, -33, -37, -39]) + (countLit q [-40, -43, -44, -45, -47, -50, -52]) := List.countP_append (p := literal q) (l₁ := [-28, -29, -30, -33, -37, -39]) (l₂ := [-40, -43, -44, -45, -47, -50, -52])
  have hm := merge_two (literal (valuationOf q) (748)) (literal (valuationOf q) (767)) (literal (valuationOf q) (776)) (countLit q [-28, -29, -30, -33, -37, -39]) (countLit q [-40, -43, -44, -45, -47, -50, -52]) (count773 q) 2 2 (meaning748 q) (meaning767 q) (meaning776 q) hs
  change valuationOf q 748 = false ∨ valuationOf q 767 = false ∨ valuationOf q 776 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause386 (q : Snake 81) (h : Conditions q) : valuation q 748 = false ∨ valuation q 767 = false ∨ valuation q 776 = true := counterClause386 (baseVal q)

theorem counterClause387 (q : Nat → Bool) : valuationOf q 748 = false ∨ valuationOf q 768 = false ∨ valuationOf q 777 = true := by
  have hs : count773 q = (countLit q [-28, -29, -30, -33, -37, -39]) + (countLit q [-40, -43, -44, -45, -47, -50, -52]) := List.countP_append (p := literal q) (l₁ := [-28, -29, -30, -33, -37, -39]) (l₂ := [-40, -43, -44, -45, -47, -50, -52])
  have hm := merge_two (literal (valuationOf q) (748)) (literal (valuationOf q) (768)) (literal (valuationOf q) (777)) (countLit q [-28, -29, -30, -33, -37, -39]) (countLit q [-40, -43, -44, -45, -47, -50, -52]) (count773 q) 2 3 (meaning748 q) (meaning768 q) (meaning777 q) hs
  change valuationOf q 748 = false ∨ valuationOf q 768 = false ∨ valuationOf q 777 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause387 (q : Snake 81) (h : Conditions q) : valuation q 748 = false ∨ valuation q 768 = false ∨ valuation q 777 = true := counterClause387 (baseVal q)

theorem counterClause388 (q : Nat → Bool) : valuationOf q 749 = false ∨ valuationOf q 767 = false ∨ valuationOf q 777 = true := by
  have hs : count773 q = (countLit q [-28, -29, -30, -33, -37, -39]) + (countLit q [-40, -43, -44, -45, -47, -50, -52]) := List.countP_append (p := literal q) (l₁ := [-28, -29, -30, -33, -37, -39]) (l₂ := [-40, -43, -44, -45, -47, -50, -52])
  have hm := merge_two (literal (valuationOf q) (749)) (literal (valuationOf q) (767)) (literal (valuationOf q) (777)) (countLit q [-28, -29, -30, -33, -37, -39]) (countLit q [-40, -43, -44, -45, -47, -50, -52]) (count773 q) 3 2 (meaning749 q) (meaning767 q) (meaning777 q) hs
  change valuationOf q 749 = false ∨ valuationOf q 767 = false ∨ valuationOf q 777 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause388 (q : Snake 81) (h : Conditions q) : valuation q 749 = false ∨ valuation q 767 = false ∨ valuation q 777 = true := counterClause388 (baseVal q)

theorem counterClause389 (q : Nat → Bool) : valuationOf q 773 = false ∨ valuationOf q 783 = true := by
  have hs : count783 q = (countLit q [-1, -3, -6, -7, -8, -13, -14, -15, -17, -20, -22, -23]) + (countLit q [-28, -29, -30, -33, -37, -39, -40, -43, -44, -45, -47, -50, -52]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -6, -7, -8, -13, -14, -15, -17, -20, -22, -23]) (l₂ := [-28, -29, -30, -33, -37, -39, -40, -43, -44, -45, -47, -50, -52])
  have hm := merge_right (literal (valuationOf q) (773)) (literal (valuationOf q) (783)) (countLit q [-1, -3, -6, -7, -8, -13, -14, -15, -17, -20, -22, -23]) (countLit q [-28, -29, -30, -33, -37, -39, -40, -43, -44, -45, -47, -50, -52]) (count783 q) 1 (meaning773 q) (meaning783 q) hs
  change valuationOf q 773 = false ∨ valuationOf q 783 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause389 (q : Snake 81) (h : Conditions q) : valuation q 773 = false ∨ valuation q 783 = true := counterClause389 (baseVal q)

theorem counterClause390 (q : Nat → Bool) : valuationOf q 774 = false ∨ valuationOf q 784 = true := by
  have hs : count783 q = (countLit q [-1, -3, -6, -7, -8, -13, -14, -15, -17, -20, -22, -23]) + (countLit q [-28, -29, -30, -33, -37, -39, -40, -43, -44, -45, -47, -50, -52]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -6, -7, -8, -13, -14, -15, -17, -20, -22, -23]) (l₂ := [-28, -29, -30, -33, -37, -39, -40, -43, -44, -45, -47, -50, -52])
  have hm := merge_right (literal (valuationOf q) (774)) (literal (valuationOf q) (784)) (countLit q [-1, -3, -6, -7, -8, -13, -14, -15, -17, -20, -22, -23]) (countLit q [-28, -29, -30, -33, -37, -39, -40, -43, -44, -45, -47, -50, -52]) (count783 q) 2 (meaning774 q) (meaning784 q) hs
  change valuationOf q 774 = false ∨ valuationOf q 784 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause390 (q : Snake 81) (h : Conditions q) : valuation q 774 = false ∨ valuation q 784 = true := counterClause390 (baseVal q)

theorem counterClause391 (q : Nat → Bool) : valuationOf q 775 = false ∨ valuationOf q 785 = true := by
  have hs : count783 q = (countLit q [-1, -3, -6, -7, -8, -13, -14, -15, -17, -20, -22, -23]) + (countLit q [-28, -29, -30, -33, -37, -39, -40, -43, -44, -45, -47, -50, -52]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -6, -7, -8, -13, -14, -15, -17, -20, -22, -23]) (l₂ := [-28, -29, -30, -33, -37, -39, -40, -43, -44, -45, -47, -50, -52])
  have hm := merge_right (literal (valuationOf q) (775)) (literal (valuationOf q) (785)) (countLit q [-1, -3, -6, -7, -8, -13, -14, -15, -17, -20, -22, -23]) (countLit q [-28, -29, -30, -33, -37, -39, -40, -43, -44, -45, -47, -50, -52]) (count783 q) 3 (meaning775 q) (meaning785 q) hs
  change valuationOf q 775 = false ∨ valuationOf q 785 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause391 (q : Snake 81) (h : Conditions q) : valuation q 775 = false ∨ valuation q 785 = true := counterClause391 (baseVal q)

theorem counterClause392 (q : Nat → Bool) : valuationOf q 776 = false ∨ valuationOf q 786 = true := by
  have hs : count783 q = (countLit q [-1, -3, -6, -7, -8, -13, -14, -15, -17, -20, -22, -23]) + (countLit q [-28, -29, -30, -33, -37, -39, -40, -43, -44, -45, -47, -50, -52]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -6, -7, -8, -13, -14, -15, -17, -20, -22, -23]) (l₂ := [-28, -29, -30, -33, -37, -39, -40, -43, -44, -45, -47, -50, -52])
  have hm := merge_right (literal (valuationOf q) (776)) (literal (valuationOf q) (786)) (countLit q [-1, -3, -6, -7, -8, -13, -14, -15, -17, -20, -22, -23]) (countLit q [-28, -29, -30, -33, -37, -39, -40, -43, -44, -45, -47, -50, -52]) (count783 q) 4 (meaning776 q) (meaning786 q) hs
  change valuationOf q 776 = false ∨ valuationOf q 786 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause392 (q : Snake 81) (h : Conditions q) : valuation q 776 = false ∨ valuation q 786 = true := counterClause392 (baseVal q)

theorem counterClause393 (q : Nat → Bool) : valuationOf q 777 = false ∨ valuationOf q 787 = true := by
  have hs : count783 q = (countLit q [-1, -3, -6, -7, -8, -13, -14, -15, -17, -20, -22, -23]) + (countLit q [-28, -29, -30, -33, -37, -39, -40, -43, -44, -45, -47, -50, -52]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -6, -7, -8, -13, -14, -15, -17, -20, -22, -23]) (l₂ := [-28, -29, -30, -33, -37, -39, -40, -43, -44, -45, -47, -50, -52])
  have hm := merge_right (literal (valuationOf q) (777)) (literal (valuationOf q) (787)) (countLit q [-1, -3, -6, -7, -8, -13, -14, -15, -17, -20, -22, -23]) (countLit q [-28, -29, -30, -33, -37, -39, -40, -43, -44, -45, -47, -50, -52]) (count783 q) 5 (meaning777 q) (meaning787 q) hs
  change valuationOf q 777 = false ∨ valuationOf q 787 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause393 (q : Snake 81) (h : Conditions q) : valuation q 777 = false ∨ valuation q 787 = true := counterClause393 (baseVal q)

theorem counterClause394 (q : Nat → Bool) : valuationOf q 727 = false ∨ valuationOf q 773 = false ∨ valuationOf q 784 = true := by
  have hs : count783 q = (countLit q [-1, -3, -6, -7, -8, -13, -14, -15, -17, -20, -22, -23]) + (countLit q [-28, -29, -30, -33, -37, -39, -40, -43, -44, -45, -47, -50, -52]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -6, -7, -8, -13, -14, -15, -17, -20, -22, -23]) (l₂ := [-28, -29, -30, -33, -37, -39, -40, -43, -44, -45, -47, -50, -52])
  have hm := merge_two (literal (valuationOf q) (727)) (literal (valuationOf q) (773)) (literal (valuationOf q) (784)) (countLit q [-1, -3, -6, -7, -8, -13, -14, -15, -17, -20, -22, -23]) (countLit q [-28, -29, -30, -33, -37, -39, -40, -43, -44, -45, -47, -50, -52]) (count783 q) 1 1 (meaning727 q) (meaning773 q) (meaning784 q) hs
  change valuationOf q 727 = false ∨ valuationOf q 773 = false ∨ valuationOf q 784 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause394 (q : Snake 81) (h : Conditions q) : valuation q 727 = false ∨ valuation q 773 = false ∨ valuation q 784 = true := counterClause394 (baseVal q)

theorem counterClause395 (q : Nat → Bool) : valuationOf q 727 = false ∨ valuationOf q 774 = false ∨ valuationOf q 785 = true := by
  have hs : count783 q = (countLit q [-1, -3, -6, -7, -8, -13, -14, -15, -17, -20, -22, -23]) + (countLit q [-28, -29, -30, -33, -37, -39, -40, -43, -44, -45, -47, -50, -52]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -6, -7, -8, -13, -14, -15, -17, -20, -22, -23]) (l₂ := [-28, -29, -30, -33, -37, -39, -40, -43, -44, -45, -47, -50, -52])
  have hm := merge_two (literal (valuationOf q) (727)) (literal (valuationOf q) (774)) (literal (valuationOf q) (785)) (countLit q [-1, -3, -6, -7, -8, -13, -14, -15, -17, -20, -22, -23]) (countLit q [-28, -29, -30, -33, -37, -39, -40, -43, -44, -45, -47, -50, -52]) (count783 q) 1 2 (meaning727 q) (meaning774 q) (meaning785 q) hs
  change valuationOf q 727 = false ∨ valuationOf q 774 = false ∨ valuationOf q 785 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause395 (q : Snake 81) (h : Conditions q) : valuation q 727 = false ∨ valuation q 774 = false ∨ valuation q 785 = true := counterClause395 (baseVal q)

theorem counterClause396 (q : Nat → Bool) : valuationOf q 727 = false ∨ valuationOf q 775 = false ∨ valuationOf q 786 = true := by
  have hs : count783 q = (countLit q [-1, -3, -6, -7, -8, -13, -14, -15, -17, -20, -22, -23]) + (countLit q [-28, -29, -30, -33, -37, -39, -40, -43, -44, -45, -47, -50, -52]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -6, -7, -8, -13, -14, -15, -17, -20, -22, -23]) (l₂ := [-28, -29, -30, -33, -37, -39, -40, -43, -44, -45, -47, -50, -52])
  have hm := merge_two (literal (valuationOf q) (727)) (literal (valuationOf q) (775)) (literal (valuationOf q) (786)) (countLit q [-1, -3, -6, -7, -8, -13, -14, -15, -17, -20, -22, -23]) (countLit q [-28, -29, -30, -33, -37, -39, -40, -43, -44, -45, -47, -50, -52]) (count783 q) 1 3 (meaning727 q) (meaning775 q) (meaning786 q) hs
  change valuationOf q 727 = false ∨ valuationOf q 775 = false ∨ valuationOf q 786 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause396 (q : Snake 81) (h : Conditions q) : valuation q 727 = false ∨ valuation q 775 = false ∨ valuation q 786 = true := counterClause396 (baseVal q)

theorem counterClause397 (q : Nat → Bool) : valuationOf q 727 = false ∨ valuationOf q 776 = false ∨ valuationOf q 787 = true := by
  have hs : count783 q = (countLit q [-1, -3, -6, -7, -8, -13, -14, -15, -17, -20, -22, -23]) + (countLit q [-28, -29, -30, -33, -37, -39, -40, -43, -44, -45, -47, -50, -52]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -6, -7, -8, -13, -14, -15, -17, -20, -22, -23]) (l₂ := [-28, -29, -30, -33, -37, -39, -40, -43, -44, -45, -47, -50, -52])
  have hm := merge_two (literal (valuationOf q) (727)) (literal (valuationOf q) (776)) (literal (valuationOf q) (787)) (countLit q [-1, -3, -6, -7, -8, -13, -14, -15, -17, -20, -22, -23]) (countLit q [-28, -29, -30, -33, -37, -39, -40, -43, -44, -45, -47, -50, -52]) (count783 q) 1 4 (meaning727 q) (meaning776 q) (meaning787 q) hs
  change valuationOf q 727 = false ∨ valuationOf q 776 = false ∨ valuationOf q 787 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause397 (q : Snake 81) (h : Conditions q) : valuation q 727 = false ∨ valuation q 776 = false ∨ valuation q 787 = true := counterClause397 (baseVal q)

theorem counterClause398 (q : Nat → Bool) : valuationOf q 728 = false ∨ valuationOf q 774 = false ∨ valuationOf q 786 = true := by
  have hs : count783 q = (countLit q [-1, -3, -6, -7, -8, -13, -14, -15, -17, -20, -22, -23]) + (countLit q [-28, -29, -30, -33, -37, -39, -40, -43, -44, -45, -47, -50, -52]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -6, -7, -8, -13, -14, -15, -17, -20, -22, -23]) (l₂ := [-28, -29, -30, -33, -37, -39, -40, -43, -44, -45, -47, -50, -52])
  have hm := merge_two (literal (valuationOf q) (728)) (literal (valuationOf q) (774)) (literal (valuationOf q) (786)) (countLit q [-1, -3, -6, -7, -8, -13, -14, -15, -17, -20, -22, -23]) (countLit q [-28, -29, -30, -33, -37, -39, -40, -43, -44, -45, -47, -50, -52]) (count783 q) 2 2 (meaning728 q) (meaning774 q) (meaning786 q) hs
  change valuationOf q 728 = false ∨ valuationOf q 774 = false ∨ valuationOf q 786 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause398 (q : Snake 81) (h : Conditions q) : valuation q 728 = false ∨ valuation q 774 = false ∨ valuation q 786 = true := counterClause398 (baseVal q)

theorem counterClause399 (q : Nat → Bool) : valuationOf q 728 = false ∨ valuationOf q 775 = false ∨ valuationOf q 787 = true := by
  have hs : count783 q = (countLit q [-1, -3, -6, -7, -8, -13, -14, -15, -17, -20, -22, -23]) + (countLit q [-28, -29, -30, -33, -37, -39, -40, -43, -44, -45, -47, -50, -52]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -6, -7, -8, -13, -14, -15, -17, -20, -22, -23]) (l₂ := [-28, -29, -30, -33, -37, -39, -40, -43, -44, -45, -47, -50, -52])
  have hm := merge_two (literal (valuationOf q) (728)) (literal (valuationOf q) (775)) (literal (valuationOf q) (787)) (countLit q [-1, -3, -6, -7, -8, -13, -14, -15, -17, -20, -22, -23]) (countLit q [-28, -29, -30, -33, -37, -39, -40, -43, -44, -45, -47, -50, -52]) (count783 q) 2 3 (meaning728 q) (meaning775 q) (meaning787 q) hs
  change valuationOf q 728 = false ∨ valuationOf q 775 = false ∨ valuationOf q 787 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause399 (q : Snake 81) (h : Conditions q) : valuation q 728 = false ∨ valuation q 775 = false ∨ valuation q 787 = true := counterClause399 (baseVal q)

theorem counterClause400 (q : Nat → Bool) : valuationOf q 729 = false ∨ valuationOf q 774 = false ∨ valuationOf q 787 = true := by
  have hs : count783 q = (countLit q [-1, -3, -6, -7, -8, -13, -14, -15, -17, -20, -22, -23]) + (countLit q [-28, -29, -30, -33, -37, -39, -40, -43, -44, -45, -47, -50, -52]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -6, -7, -8, -13, -14, -15, -17, -20, -22, -23]) (l₂ := [-28, -29, -30, -33, -37, -39, -40, -43, -44, -45, -47, -50, -52])
  have hm := merge_two (literal (valuationOf q) (729)) (literal (valuationOf q) (774)) (literal (valuationOf q) (787)) (countLit q [-1, -3, -6, -7, -8, -13, -14, -15, -17, -20, -22, -23]) (countLit q [-28, -29, -30, -33, -37, -39, -40, -43, -44, -45, -47, -50, -52]) (count783 q) 3 2 (meaning729 q) (meaning774 q) (meaning787 q) hs
  change valuationOf q 729 = false ∨ valuationOf q 774 = false ∨ valuationOf q 787 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause400 (q : Snake 81) (h : Conditions q) : valuation q 729 = false ∨ valuation q 774 = false ∨ valuation q 787 = true := counterClause400 (baseVal q)

theorem counterClause401 (q : Nat → Bool) : valuationOf q 730 = false ∨ valuationOf q 773 = false ∨ valuationOf q 787 = true := by
  have hs : count783 q = (countLit q [-1, -3, -6, -7, -8, -13, -14, -15, -17, -20, -22, -23]) + (countLit q [-28, -29, -30, -33, -37, -39, -40, -43, -44, -45, -47, -50, -52]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -6, -7, -8, -13, -14, -15, -17, -20, -22, -23]) (l₂ := [-28, -29, -30, -33, -37, -39, -40, -43, -44, -45, -47, -50, -52])
  have hm := merge_two (literal (valuationOf q) (730)) (literal (valuationOf q) (773)) (literal (valuationOf q) (787)) (countLit q [-1, -3, -6, -7, -8, -13, -14, -15, -17, -20, -22, -23]) (countLit q [-28, -29, -30, -33, -37, -39, -40, -43, -44, -45, -47, -50, -52]) (count783 q) 4 1 (meaning730 q) (meaning773 q) (meaning787 q) hs
  change valuationOf q 730 = false ∨ valuationOf q 773 = false ∨ valuationOf q 787 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause401 (q : Snake 81) (h : Conditions q) : valuation q 730 = false ∨ valuation q 773 = false ∨ valuation q 787 = true := counterClause401 (baseVal q)

theorem counterClause402 (q : Nat → Bool) : valuationOf q 730 = false ∨ valuationOf q 775 = false ∨ valuationOf q 789 = true := by
  have hs : count783 q = (countLit q [-1, -3, -6, -7, -8, -13, -14, -15, -17, -20, -22, -23]) + (countLit q [-28, -29, -30, -33, -37, -39, -40, -43, -44, -45, -47, -50, -52]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -6, -7, -8, -13, -14, -15, -17, -20, -22, -23]) (l₂ := [-28, -29, -30, -33, -37, -39, -40, -43, -44, -45, -47, -50, -52])
  have hm := merge_two (literal (valuationOf q) (730)) (literal (valuationOf q) (775)) (literal (valuationOf q) (789)) (countLit q [-1, -3, -6, -7, -8, -13, -14, -15, -17, -20, -22, -23]) (countLit q [-28, -29, -30, -33, -37, -39, -40, -43, -44, -45, -47, -50, -52]) (count783 q) 4 3 (meaning730 q) (meaning775 q) (meaning789 q) hs
  change valuationOf q 730 = false ∨ valuationOf q 775 = false ∨ valuationOf q 789 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause402 (q : Snake 81) (h : Conditions q) : valuation q 730 = false ∨ valuation q 775 = false ∨ valuation q 789 = true := counterClause402 (baseVal q)

theorem counterClause403 (q : Nat → Bool) : valuationOf q 67 = true ∨ valuationOf q 798 = true := by
  have hs : count798 q = (countLit q [-65]) + (countLit q [-67]) := List.countP_append (p := literal q) (l₁ := [-65]) (l₂ := [-67])
  have hm := merge_right (literal (valuationOf q) (-67)) (literal (valuationOf q) (798)) (countLit q [-65]) (countLit q [-67]) (count798 q) 1 (meaningNeg67 q) (meaning798 q) hs
  change (! (valuationOf q 67)) = false ∨ valuationOf q 798 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause403 (q : Snake 81) (h : Conditions q) : valuation q 67 = true ∨ valuation q 798 = true := counterClause403 (baseVal q)

theorem counterClause404 (q : Nat → Bool) : valuationOf q 65 = true ∨ valuationOf q 798 = true := by
  have hs : count798 q = (countLit q [-65]) + (countLit q [-67]) := List.countP_append (p := literal q) (l₁ := [-65]) (l₂ := [-67])
  have hm := merge_left (literal (valuationOf q) (-65)) (literal (valuationOf q) (798)) (countLit q [-65]) (countLit q [-67]) (count798 q) 1 (meaningNeg65 q) (meaning798 q) hs
  change (! (valuationOf q 65)) = false ∨ valuationOf q 798 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause404 (q : Snake 81) (h : Conditions q) : valuation q 65 = true ∨ valuation q 798 = true := counterClause404 (baseVal q)

theorem counterClause405 (q : Nat → Bool) : valuationOf q 65 = true ∨ valuationOf q 67 = true ∨ valuationOf q 799 = true := by
  have hs : count798 q = (countLit q [-65]) + (countLit q [-67]) := List.countP_append (p := literal q) (l₁ := [-65]) (l₂ := [-67])
  have hm := merge_two (literal (valuationOf q) (-65)) (literal (valuationOf q) (-67)) (literal (valuationOf q) (799)) (countLit q [-65]) (countLit q [-67]) (count798 q) 1 1 (meaningNeg65 q) (meaningNeg67 q) (meaning799 q) hs
  change (! (valuationOf q 65)) = false ∨ (! (valuationOf q 67)) = false ∨ valuationOf q 799 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause405 (q : Snake 81) (h : Conditions q) : valuation q 65 = true ∨ valuation q 67 = true ∨ valuation q 799 = true := counterClause405 (baseVal q)

theorem counterClause406 (q : Nat → Bool) : valuationOf q 798 = false ∨ valuationOf q 800 = true := by
  have hs : count800 q = (countLit q [-62]) + (countLit q [-65, -67]) := List.countP_append (p := literal q) (l₁ := [-62]) (l₂ := [-65, -67])
  have hm := merge_right (literal (valuationOf q) (798)) (literal (valuationOf q) (800)) (countLit q [-62]) (countLit q [-65, -67]) (count800 q) 1 (meaning798 q) (meaning800 q) hs
  change valuationOf q 798 = false ∨ valuationOf q 800 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause406 (q : Snake 81) (h : Conditions q) : valuation q 798 = false ∨ valuation q 800 = true := counterClause406 (baseVal q)

theorem counterClause407 (q : Nat → Bool) : valuationOf q 799 = false ∨ valuationOf q 801 = true := by
  have hs : count800 q = (countLit q [-62]) + (countLit q [-65, -67]) := List.countP_append (p := literal q) (l₁ := [-62]) (l₂ := [-65, -67])
  have hm := merge_right (literal (valuationOf q) (799)) (literal (valuationOf q) (801)) (countLit q [-62]) (countLit q [-65, -67]) (count800 q) 2 (meaning799 q) (meaning801 q) hs
  change valuationOf q 799 = false ∨ valuationOf q 801 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause407 (q : Snake 81) (h : Conditions q) : valuation q 799 = false ∨ valuation q 801 = true := counterClause407 (baseVal q)

theorem counterClause408 (q : Nat → Bool) : valuationOf q 62 = true ∨ valuationOf q 800 = true := by
  have hs : count800 q = (countLit q [-62]) + (countLit q [-65, -67]) := List.countP_append (p := literal q) (l₁ := [-62]) (l₂ := [-65, -67])
  have hm := merge_left (literal (valuationOf q) (-62)) (literal (valuationOf q) (800)) (countLit q [-62]) (countLit q [-65, -67]) (count800 q) 1 (meaningNeg62 q) (meaning800 q) hs
  change (! (valuationOf q 62)) = false ∨ valuationOf q 800 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause408 (q : Snake 81) (h : Conditions q) : valuation q 62 = true ∨ valuation q 800 = true := counterClause408 (baseVal q)

theorem counterClause409 (q : Nat → Bool) : valuationOf q 62 = true ∨ valuationOf q 798 = false ∨ valuationOf q 801 = true := by
  have hs : count800 q = (countLit q [-62]) + (countLit q [-65, -67]) := List.countP_append (p := literal q) (l₁ := [-62]) (l₂ := [-65, -67])
  have hm := merge_two (literal (valuationOf q) (-62)) (literal (valuationOf q) (798)) (literal (valuationOf q) (801)) (countLit q [-62]) (countLit q [-65, -67]) (count800 q) 1 1 (meaningNeg62 q) (meaning798 q) (meaning801 q) hs
  change (! (valuationOf q 62)) = false ∨ valuationOf q 798 = false ∨ valuationOf q 801 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause409 (q : Snake 81) (h : Conditions q) : valuation q 62 = true ∨ valuation q 798 = false ∨ valuation q 801 = true := counterClause409 (baseVal q)

theorem counterClause410 (q : Nat → Bool) : valuationOf q 62 = true ∨ valuationOf q 799 = false ∨ valuationOf q 802 = true := by
  have hs : count800 q = (countLit q [-62]) + (countLit q [-65, -67]) := List.countP_append (p := literal q) (l₁ := [-62]) (l₂ := [-65, -67])
  have hm := merge_two (literal (valuationOf q) (-62)) (literal (valuationOf q) (799)) (literal (valuationOf q) (802)) (countLit q [-62]) (countLit q [-65, -67]) (count800 q) 1 2 (meaningNeg62 q) (meaning799 q) (meaning802 q) hs
  change (! (valuationOf q 62)) = false ∨ valuationOf q 799 = false ∨ valuationOf q 802 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause410 (q : Snake 81) (h : Conditions q) : valuation q 62 = true ∨ valuation q 799 = false ∨ valuation q 802 = true := counterClause410 (baseVal q)

theorem counterClause411 (q : Nat → Bool) : valuationOf q 800 = false ∨ valuationOf q 803 = true := by
  have hs : count803 q = (countLit q [-53, -58, -59]) + (countLit q [-62, -65, -67]) := List.countP_append (p := literal q) (l₁ := [-53, -58, -59]) (l₂ := [-62, -65, -67])
  have hm := merge_right (literal (valuationOf q) (800)) (literal (valuationOf q) (803)) (countLit q [-53, -58, -59]) (countLit q [-62, -65, -67]) (count803 q) 1 (meaning800 q) (meaning803 q) hs
  change valuationOf q 800 = false ∨ valuationOf q 803 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause411 (q : Snake 81) (h : Conditions q) : valuation q 800 = false ∨ valuation q 803 = true := counterClause411 (baseVal q)

theorem counterClause412 (q : Nat → Bool) : valuationOf q 801 = false ∨ valuationOf q 804 = true := by
  have hs : count803 q = (countLit q [-53, -58, -59]) + (countLit q [-62, -65, -67]) := List.countP_append (p := literal q) (l₁ := [-53, -58, -59]) (l₂ := [-62, -65, -67])
  have hm := merge_right (literal (valuationOf q) (801)) (literal (valuationOf q) (804)) (countLit q [-53, -58, -59]) (countLit q [-62, -65, -67]) (count803 q) 2 (meaning801 q) (meaning804 q) hs
  change valuationOf q 801 = false ∨ valuationOf q 804 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause412 (q : Snake 81) (h : Conditions q) : valuation q 801 = false ∨ valuation q 804 = true := counterClause412 (baseVal q)

theorem counterClause413 (q : Nat → Bool) : valuationOf q 802 = false ∨ valuationOf q 805 = true := by
  have hs : count803 q = (countLit q [-53, -58, -59]) + (countLit q [-62, -65, -67]) := List.countP_append (p := literal q) (l₁ := [-53, -58, -59]) (l₂ := [-62, -65, -67])
  have hm := merge_right (literal (valuationOf q) (802)) (literal (valuationOf q) (805)) (countLit q [-53, -58, -59]) (countLit q [-62, -65, -67]) (count803 q) 3 (meaning802 q) (meaning805 q) hs
  change valuationOf q 802 = false ∨ valuationOf q 805 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause413 (q : Snake 81) (h : Conditions q) : valuation q 802 = false ∨ valuation q 805 = true := counterClause413 (baseVal q)

theorem counterClause414 (q : Nat → Bool) : valuationOf q 73 = true ∨ valuationOf q 809 = true := by
  have hs : count809 q = (countLit q [-71]) + (countLit q [-73]) := List.countP_append (p := literal q) (l₁ := [-71]) (l₂ := [-73])
  have hm := merge_right (literal (valuationOf q) (-73)) (literal (valuationOf q) (809)) (countLit q [-71]) (countLit q [-73]) (count809 q) 1 (meaningNeg73 q) (meaning809 q) hs
  change (! (valuationOf q 73)) = false ∨ valuationOf q 809 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause414 (q : Snake 81) (h : Conditions q) : valuation q 73 = true ∨ valuation q 809 = true := counterClause414 (baseVal q)

theorem counterClause415 (q : Nat → Bool) : valuationOf q 71 = true ∨ valuationOf q 809 = true := by
  have hs : count809 q = (countLit q [-71]) + (countLit q [-73]) := List.countP_append (p := literal q) (l₁ := [-71]) (l₂ := [-73])
  have hm := merge_left (literal (valuationOf q) (-71)) (literal (valuationOf q) (809)) (countLit q [-71]) (countLit q [-73]) (count809 q) 1 (meaningNeg71 q) (meaning809 q) hs
  change (! (valuationOf q 71)) = false ∨ valuationOf q 809 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause415 (q : Snake 81) (h : Conditions q) : valuation q 71 = true ∨ valuation q 809 = true := counterClause415 (baseVal q)

theorem counterClause416 (q : Nat → Bool) : valuationOf q 71 = true ∨ valuationOf q 73 = true ∨ valuationOf q 810 = true := by
  have hs : count809 q = (countLit q [-71]) + (countLit q [-73]) := List.countP_append (p := literal q) (l₁ := [-71]) (l₂ := [-73])
  have hm := merge_two (literal (valuationOf q) (-71)) (literal (valuationOf q) (-73)) (literal (valuationOf q) (810)) (countLit q [-71]) (countLit q [-73]) (count809 q) 1 1 (meaningNeg71 q) (meaningNeg73 q) (meaning810 q) hs
  change (! (valuationOf q 71)) = false ∨ (! (valuationOf q 73)) = false ∨ valuationOf q 810 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause416 (q : Snake 81) (h : Conditions q) : valuation q 71 = true ∨ valuation q 73 = true ∨ valuation q 810 = true := counterClause416 (baseVal q)

theorem block12 (q : Snake 81) (h : Conditions q) : B112E075.Block12 (valuation q) :=
  ⟨clause385 q h, clause386 q h, clause387 q h, clause388 q h, clause389 q h, clause390 q h, clause391 q h, clause392 q h, clause393 q h, clause394 q h, clause395 q h, clause396 q h, clause397 q h, clause398 q h, clause399 q h, clause400 q h, clause401 q h, clause402 q h, clause403 q h, clause404 q h, clause405 q h, clause406 q h, clause407 q h, clause408 q h, clause409 q h, clause410 q h, clause411 q h, clause412 q h, clause413 q h, clause414 q h, clause415 q h, clause416 q h⟩

end
end Snake9.Regrowth.E112075
