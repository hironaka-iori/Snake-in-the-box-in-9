import E112051Semantics
import B112E051Inputs
namespace Snake9.Regrowth.E112051
noncomputable section
local instance blockDec16 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause513 (q : Nat → Bool) : valuationOf q 807 = false ∨ valuationOf q 811 = true := by
  have hs : count810 q = (countLit q [-24, -26]) + (countLit q [-27, -30]) := List.countP_append (p := literal q) (l₁ := [-24, -26]) (l₂ := [-27, -30])
  have hm := merge_left (literal (valuationOf q) (807)) (literal (valuationOf q) (811)) (countLit q [-24, -26]) (countLit q [-27, -30]) (count810 q) 2 (meaning807 q) (meaning811 q) hs
  change valuationOf q 807 = false ∨ valuationOf q 811 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause513 (q : Snake 81) (h : Conditions q) : valuation q 807 = false ∨ valuation q 811 = true := counterClause513 (baseVal q)

theorem counterClause514 (q : Nat → Bool) : valuationOf q 807 = false ∨ valuationOf q 808 = false ∨ valuationOf q 812 = true := by
  have hs : count810 q = (countLit q [-24, -26]) + (countLit q [-27, -30]) := List.countP_append (p := literal q) (l₁ := [-24, -26]) (l₂ := [-27, -30])
  have hm := merge_two (literal (valuationOf q) (807)) (literal (valuationOf q) (808)) (literal (valuationOf q) (812)) (countLit q [-24, -26]) (countLit q [-27, -30]) (count810 q) 2 1 (meaning807 q) (meaning808 q) (meaning812 q) hs
  change valuationOf q 807 = false ∨ valuationOf q 808 = false ∨ valuationOf q 812 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause514 (q : Snake 81) (h : Conditions q) : valuation q 807 = false ∨ valuation q 808 = false ∨ valuation q 812 = true := counterClause514 (baseVal q)

theorem counterClause515 (q : Nat → Bool) : valuationOf q 810 = false ∨ valuationOf q 814 = true := by
  have hs : count814 q = (countLit q [-16, -17, -20]) + (countLit q [-24, -26, -27, -30]) := List.countP_append (p := literal q) (l₁ := [-16, -17, -20]) (l₂ := [-24, -26, -27, -30])
  have hm := merge_right (literal (valuationOf q) (810)) (literal (valuationOf q) (814)) (countLit q [-16, -17, -20]) (countLit q [-24, -26, -27, -30]) (count814 q) 1 (meaning810 q) (meaning814 q) hs
  change valuationOf q 810 = false ∨ valuationOf q 814 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause515 (q : Snake 81) (h : Conditions q) : valuation q 810 = false ∨ valuation q 814 = true := counterClause515 (baseVal q)

theorem counterClause516 (q : Nat → Bool) : valuationOf q 811 = false ∨ valuationOf q 815 = true := by
  have hs : count814 q = (countLit q [-16, -17, -20]) + (countLit q [-24, -26, -27, -30]) := List.countP_append (p := literal q) (l₁ := [-16, -17, -20]) (l₂ := [-24, -26, -27, -30])
  have hm := merge_right (literal (valuationOf q) (811)) (literal (valuationOf q) (815)) (countLit q [-16, -17, -20]) (countLit q [-24, -26, -27, -30]) (count814 q) 2 (meaning811 q) (meaning815 q) hs
  change valuationOf q 811 = false ∨ valuationOf q 815 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause516 (q : Snake 81) (h : Conditions q) : valuation q 811 = false ∨ valuation q 815 = true := counterClause516 (baseVal q)

theorem counterClause517 (q : Nat → Bool) : valuationOf q 812 = false ∨ valuationOf q 816 = true := by
  have hs : count814 q = (countLit q [-16, -17, -20]) + (countLit q [-24, -26, -27, -30]) := List.countP_append (p := literal q) (l₁ := [-16, -17, -20]) (l₂ := [-24, -26, -27, -30])
  have hm := merge_right (literal (valuationOf q) (812)) (literal (valuationOf q) (816)) (countLit q [-16, -17, -20]) (countLit q [-24, -26, -27, -30]) (count814 q) 3 (meaning812 q) (meaning816 q) hs
  change valuationOf q 812 = false ∨ valuationOf q 816 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause517 (q : Snake 81) (h : Conditions q) : valuation q 812 = false ∨ valuation q 816 = true := counterClause517 (baseVal q)

theorem counterClause518 (q : Nat → Bool) : valuationOf q 803 = false ∨ valuationOf q 814 = true := by
  have hs : count814 q = (countLit q [-16, -17, -20]) + (countLit q [-24, -26, -27, -30]) := List.countP_append (p := literal q) (l₁ := [-16, -17, -20]) (l₂ := [-24, -26, -27, -30])
  have hm := merge_left (literal (valuationOf q) (803)) (literal (valuationOf q) (814)) (countLit q [-16, -17, -20]) (countLit q [-24, -26, -27, -30]) (count814 q) 1 (meaning803 q) (meaning814 q) hs
  change valuationOf q 803 = false ∨ valuationOf q 814 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause518 (q : Snake 81) (h : Conditions q) : valuation q 803 = false ∨ valuation q 814 = true := counterClause518 (baseVal q)

theorem counterClause519 (q : Nat → Bool) : valuationOf q 803 = false ∨ valuationOf q 810 = false ∨ valuationOf q 815 = true := by
  have hs : count814 q = (countLit q [-16, -17, -20]) + (countLit q [-24, -26, -27, -30]) := List.countP_append (p := literal q) (l₁ := [-16, -17, -20]) (l₂ := [-24, -26, -27, -30])
  have hm := merge_two (literal (valuationOf q) (803)) (literal (valuationOf q) (810)) (literal (valuationOf q) (815)) (countLit q [-16, -17, -20]) (countLit q [-24, -26, -27, -30]) (count814 q) 1 1 (meaning803 q) (meaning810 q) (meaning815 q) hs
  change valuationOf q 803 = false ∨ valuationOf q 810 = false ∨ valuationOf q 815 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause519 (q : Snake 81) (h : Conditions q) : valuation q 803 = false ∨ valuation q 810 = false ∨ valuation q 815 = true := counterClause519 (baseVal q)

theorem counterClause520 (q : Nat → Bool) : valuationOf q 803 = false ∨ valuationOf q 811 = false ∨ valuationOf q 816 = true := by
  have hs : count814 q = (countLit q [-16, -17, -20]) + (countLit q [-24, -26, -27, -30]) := List.countP_append (p := literal q) (l₁ := [-16, -17, -20]) (l₂ := [-24, -26, -27, -30])
  have hm := merge_two (literal (valuationOf q) (803)) (literal (valuationOf q) (811)) (literal (valuationOf q) (816)) (countLit q [-16, -17, -20]) (countLit q [-24, -26, -27, -30]) (count814 q) 1 2 (meaning803 q) (meaning811 q) (meaning816 q) hs
  change valuationOf q 803 = false ∨ valuationOf q 811 = false ∨ valuationOf q 816 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause520 (q : Snake 81) (h : Conditions q) : valuation q 803 = false ∨ valuation q 811 = false ∨ valuation q 816 = true := counterClause520 (baseVal q)

theorem counterClause521 (q : Nat → Bool) : valuationOf q 803 = false ∨ valuationOf q 812 = false ∨ valuationOf q 817 = true := by
  have hs : count814 q = (countLit q [-16, -17, -20]) + (countLit q [-24, -26, -27, -30]) := List.countP_append (p := literal q) (l₁ := [-16, -17, -20]) (l₂ := [-24, -26, -27, -30])
  have hm := merge_two (literal (valuationOf q) (803)) (literal (valuationOf q) (812)) (literal (valuationOf q) (817)) (countLit q [-16, -17, -20]) (countLit q [-24, -26, -27, -30]) (count814 q) 1 3 (meaning803 q) (meaning812 q) (meaning817 q) hs
  change valuationOf q 803 = false ∨ valuationOf q 812 = false ∨ valuationOf q 817 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause521 (q : Snake 81) (h : Conditions q) : valuation q 803 = false ∨ valuation q 812 = false ∨ valuation q 817 = true := counterClause521 (baseVal q)

theorem counterClause522 (q : Nat → Bool) : valuationOf q 804 = false ∨ valuationOf q 815 = true := by
  have hs : count814 q = (countLit q [-16, -17, -20]) + (countLit q [-24, -26, -27, -30]) := List.countP_append (p := literal q) (l₁ := [-16, -17, -20]) (l₂ := [-24, -26, -27, -30])
  have hm := merge_left (literal (valuationOf q) (804)) (literal (valuationOf q) (815)) (countLit q [-16, -17, -20]) (countLit q [-24, -26, -27, -30]) (count814 q) 2 (meaning804 q) (meaning815 q) hs
  change valuationOf q 804 = false ∨ valuationOf q 815 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause522 (q : Snake 81) (h : Conditions q) : valuation q 804 = false ∨ valuation q 815 = true := counterClause522 (baseVal q)

theorem counterClause523 (q : Nat → Bool) : valuationOf q 804 = false ∨ valuationOf q 810 = false ∨ valuationOf q 816 = true := by
  have hs : count814 q = (countLit q [-16, -17, -20]) + (countLit q [-24, -26, -27, -30]) := List.countP_append (p := literal q) (l₁ := [-16, -17, -20]) (l₂ := [-24, -26, -27, -30])
  have hm := merge_two (literal (valuationOf q) (804)) (literal (valuationOf q) (810)) (literal (valuationOf q) (816)) (countLit q [-16, -17, -20]) (countLit q [-24, -26, -27, -30]) (count814 q) 2 1 (meaning804 q) (meaning810 q) (meaning816 q) hs
  change valuationOf q 804 = false ∨ valuationOf q 810 = false ∨ valuationOf q 816 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause523 (q : Snake 81) (h : Conditions q) : valuation q 804 = false ∨ valuation q 810 = false ∨ valuation q 816 = true := counterClause523 (baseVal q)

theorem counterClause524 (q : Nat → Bool) : valuationOf q 804 = false ∨ valuationOf q 811 = false ∨ valuationOf q 817 = true := by
  have hs : count814 q = (countLit q [-16, -17, -20]) + (countLit q [-24, -26, -27, -30]) := List.countP_append (p := literal q) (l₁ := [-16, -17, -20]) (l₂ := [-24, -26, -27, -30])
  have hm := merge_two (literal (valuationOf q) (804)) (literal (valuationOf q) (811)) (literal (valuationOf q) (817)) (countLit q [-16, -17, -20]) (countLit q [-24, -26, -27, -30]) (count814 q) 2 2 (meaning804 q) (meaning811 q) (meaning817 q) hs
  change valuationOf q 804 = false ∨ valuationOf q 811 = false ∨ valuationOf q 817 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause524 (q : Snake 81) (h : Conditions q) : valuation q 804 = false ∨ valuation q 811 = false ∨ valuation q 817 = true := counterClause524 (baseVal q)

theorem counterClause525 (q : Nat → Bool) : valuationOf q 805 = false ∨ valuationOf q 810 = false ∨ valuationOf q 817 = true := by
  have hs : count814 q = (countLit q [-16, -17, -20]) + (countLit q [-24, -26, -27, -30]) := List.countP_append (p := literal q) (l₁ := [-16, -17, -20]) (l₂ := [-24, -26, -27, -30])
  have hm := merge_two (literal (valuationOf q) (805)) (literal (valuationOf q) (810)) (literal (valuationOf q) (817)) (countLit q [-16, -17, -20]) (countLit q [-24, -26, -27, -30]) (count814 q) 3 1 (meaning805 q) (meaning810 q) (meaning817 q) hs
  change valuationOf q 805 = false ∨ valuationOf q 810 = false ∨ valuationOf q 817 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause525 (q : Snake 81) (h : Conditions q) : valuation q 805 = false ∨ valuation q 810 = false ∨ valuation q 817 = true := counterClause525 (baseVal q)

theorem counterClause526 (q : Nat → Bool) : valuationOf q 815 = false ∨ valuationOf q 822 = true := by
  have hs : count821 q = (countLit q [-1, -3, -6, -8, -9, -10, -15]) + (countLit q [-16, -17, -20, -24, -26, -27, -30]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -6, -8, -9, -10, -15]) (l₂ := [-16, -17, -20, -24, -26, -27, -30])
  have hm := merge_right (literal (valuationOf q) (815)) (literal (valuationOf q) (822)) (countLit q [-1, -3, -6, -8, -9, -10, -15]) (countLit q [-16, -17, -20, -24, -26, -27, -30]) (count821 q) 2 (meaning815 q) (meaning822 q) hs
  change valuationOf q 815 = false ∨ valuationOf q 822 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause526 (q : Snake 81) (h : Conditions q) : valuation q 815 = false ∨ valuation q 822 = true := counterClause526 (baseVal q)

theorem counterClause527 (q : Nat → Bool) : valuationOf q 816 = false ∨ valuationOf q 823 = true := by
  have hs : count821 q = (countLit q [-1, -3, -6, -8, -9, -10, -15]) + (countLit q [-16, -17, -20, -24, -26, -27, -30]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -6, -8, -9, -10, -15]) (l₂ := [-16, -17, -20, -24, -26, -27, -30])
  have hm := merge_right (literal (valuationOf q) (816)) (literal (valuationOf q) (823)) (countLit q [-1, -3, -6, -8, -9, -10, -15]) (countLit q [-16, -17, -20, -24, -26, -27, -30]) (count821 q) 3 (meaning816 q) (meaning823 q) hs
  change valuationOf q 816 = false ∨ valuationOf q 823 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause527 (q : Snake 81) (h : Conditions q) : valuation q 816 = false ∨ valuation q 823 = true := counterClause527 (baseVal q)

theorem counterClause528 (q : Nat → Bool) : valuationOf q 817 = false ∨ valuationOf q 824 = true := by
  have hs : count821 q = (countLit q [-1, -3, -6, -8, -9, -10, -15]) + (countLit q [-16, -17, -20, -24, -26, -27, -30]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -6, -8, -9, -10, -15]) (l₂ := [-16, -17, -20, -24, -26, -27, -30])
  have hm := merge_right (literal (valuationOf q) (817)) (literal (valuationOf q) (824)) (countLit q [-1, -3, -6, -8, -9, -10, -15]) (countLit q [-16, -17, -20, -24, -26, -27, -30]) (count821 q) 4 (meaning817 q) (meaning824 q) hs
  change valuationOf q 817 = false ∨ valuationOf q 824 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause528 (q : Snake 81) (h : Conditions q) : valuation q 817 = false ∨ valuation q 824 = true := counterClause528 (baseVal q)

theorem counterClause529 (q : Nat → Bool) : valuationOf q 794 = false ∨ valuationOf q 814 = false ∨ valuationOf q 822 = true := by
  have hs : count821 q = (countLit q [-1, -3, -6, -8, -9, -10, -15]) + (countLit q [-16, -17, -20, -24, -26, -27, -30]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -6, -8, -9, -10, -15]) (l₂ := [-16, -17, -20, -24, -26, -27, -30])
  have hm := merge_two (literal (valuationOf q) (794)) (literal (valuationOf q) (814)) (literal (valuationOf q) (822)) (countLit q [-1, -3, -6, -8, -9, -10, -15]) (countLit q [-16, -17, -20, -24, -26, -27, -30]) (count821 q) 1 1 (meaning794 q) (meaning814 q) (meaning822 q) hs
  change valuationOf q 794 = false ∨ valuationOf q 814 = false ∨ valuationOf q 822 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause529 (q : Snake 81) (h : Conditions q) : valuation q 794 = false ∨ valuation q 814 = false ∨ valuation q 822 = true := counterClause529 (baseVal q)

theorem counterClause530 (q : Nat → Bool) : valuationOf q 794 = false ∨ valuationOf q 815 = false ∨ valuationOf q 823 = true := by
  have hs : count821 q = (countLit q [-1, -3, -6, -8, -9, -10, -15]) + (countLit q [-16, -17, -20, -24, -26, -27, -30]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -6, -8, -9, -10, -15]) (l₂ := [-16, -17, -20, -24, -26, -27, -30])
  have hm := merge_two (literal (valuationOf q) (794)) (literal (valuationOf q) (815)) (literal (valuationOf q) (823)) (countLit q [-1, -3, -6, -8, -9, -10, -15]) (countLit q [-16, -17, -20, -24, -26, -27, -30]) (count821 q) 1 2 (meaning794 q) (meaning815 q) (meaning823 q) hs
  change valuationOf q 794 = false ∨ valuationOf q 815 = false ∨ valuationOf q 823 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause530 (q : Snake 81) (h : Conditions q) : valuation q 794 = false ∨ valuation q 815 = false ∨ valuation q 823 = true := counterClause530 (baseVal q)

theorem counterClause531 (q : Nat → Bool) : valuationOf q 794 = false ∨ valuationOf q 816 = false ∨ valuationOf q 824 = true := by
  have hs : count821 q = (countLit q [-1, -3, -6, -8, -9, -10, -15]) + (countLit q [-16, -17, -20, -24, -26, -27, -30]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -6, -8, -9, -10, -15]) (l₂ := [-16, -17, -20, -24, -26, -27, -30])
  have hm := merge_two (literal (valuationOf q) (794)) (literal (valuationOf q) (816)) (literal (valuationOf q) (824)) (countLit q [-1, -3, -6, -8, -9, -10, -15]) (countLit q [-16, -17, -20, -24, -26, -27, -30]) (count821 q) 1 3 (meaning794 q) (meaning816 q) (meaning824 q) hs
  change valuationOf q 794 = false ∨ valuationOf q 816 = false ∨ valuationOf q 824 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause531 (q : Snake 81) (h : Conditions q) : valuation q 794 = false ∨ valuation q 816 = false ∨ valuation q 824 = true := counterClause531 (baseVal q)

theorem counterClause532 (q : Nat → Bool) : valuationOf q 795 = false ∨ valuationOf q 822 = true := by
  have hs : count821 q = (countLit q [-1, -3, -6, -8, -9, -10, -15]) + (countLit q [-16, -17, -20, -24, -26, -27, -30]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -6, -8, -9, -10, -15]) (l₂ := [-16, -17, -20, -24, -26, -27, -30])
  have hm := merge_left (literal (valuationOf q) (795)) (literal (valuationOf q) (822)) (countLit q [-1, -3, -6, -8, -9, -10, -15]) (countLit q [-16, -17, -20, -24, -26, -27, -30]) (count821 q) 2 (meaning795 q) (meaning822 q) hs
  change valuationOf q 795 = false ∨ valuationOf q 822 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause532 (q : Snake 81) (h : Conditions q) : valuation q 795 = false ∨ valuation q 822 = true := counterClause532 (baseVal q)

theorem counterClause533 (q : Nat → Bool) : valuationOf q 795 = false ∨ valuationOf q 814 = false ∨ valuationOf q 823 = true := by
  have hs : count821 q = (countLit q [-1, -3, -6, -8, -9, -10, -15]) + (countLit q [-16, -17, -20, -24, -26, -27, -30]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -6, -8, -9, -10, -15]) (l₂ := [-16, -17, -20, -24, -26, -27, -30])
  have hm := merge_two (literal (valuationOf q) (795)) (literal (valuationOf q) (814)) (literal (valuationOf q) (823)) (countLit q [-1, -3, -6, -8, -9, -10, -15]) (countLit q [-16, -17, -20, -24, -26, -27, -30]) (count821 q) 2 1 (meaning795 q) (meaning814 q) (meaning823 q) hs
  change valuationOf q 795 = false ∨ valuationOf q 814 = false ∨ valuationOf q 823 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause533 (q : Snake 81) (h : Conditions q) : valuation q 795 = false ∨ valuation q 814 = false ∨ valuation q 823 = true := counterClause533 (baseVal q)

theorem counterClause534 (q : Nat → Bool) : valuationOf q 795 = false ∨ valuationOf q 815 = false ∨ valuationOf q 824 = true := by
  have hs : count821 q = (countLit q [-1, -3, -6, -8, -9, -10, -15]) + (countLit q [-16, -17, -20, -24, -26, -27, -30]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -6, -8, -9, -10, -15]) (l₂ := [-16, -17, -20, -24, -26, -27, -30])
  have hm := merge_two (literal (valuationOf q) (795)) (literal (valuationOf q) (815)) (literal (valuationOf q) (824)) (countLit q [-1, -3, -6, -8, -9, -10, -15]) (countLit q [-16, -17, -20, -24, -26, -27, -30]) (count821 q) 2 2 (meaning795 q) (meaning815 q) (meaning824 q) hs
  change valuationOf q 795 = false ∨ valuationOf q 815 = false ∨ valuationOf q 824 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause534 (q : Snake 81) (h : Conditions q) : valuation q 795 = false ∨ valuation q 815 = false ∨ valuation q 824 = true := counterClause534 (baseVal q)

theorem counterClause535 (q : Nat → Bool) : valuationOf q 795 = false ∨ valuationOf q 816 = false ∨ valuationOf q 825 = true := by
  have hs : count821 q = (countLit q [-1, -3, -6, -8, -9, -10, -15]) + (countLit q [-16, -17, -20, -24, -26, -27, -30]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -6, -8, -9, -10, -15]) (l₂ := [-16, -17, -20, -24, -26, -27, -30])
  have hm := merge_two (literal (valuationOf q) (795)) (literal (valuationOf q) (816)) (literal (valuationOf q) (825)) (countLit q [-1, -3, -6, -8, -9, -10, -15]) (countLit q [-16, -17, -20, -24, -26, -27, -30]) (count821 q) 2 3 (meaning795 q) (meaning816 q) (meaning825 q) hs
  change valuationOf q 795 = false ∨ valuationOf q 816 = false ∨ valuationOf q 825 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause535 (q : Snake 81) (h : Conditions q) : valuation q 795 = false ∨ valuation q 816 = false ∨ valuation q 825 = true := counterClause535 (baseVal q)

theorem counterClause536 (q : Nat → Bool) : valuationOf q 795 = false ∨ valuationOf q 817 = false ∨ valuationOf q 826 = true := by
  have hs : count821 q = (countLit q [-1, -3, -6, -8, -9, -10, -15]) + (countLit q [-16, -17, -20, -24, -26, -27, -30]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -6, -8, -9, -10, -15]) (l₂ := [-16, -17, -20, -24, -26, -27, -30])
  have hm := merge_two (literal (valuationOf q) (795)) (literal (valuationOf q) (817)) (literal (valuationOf q) (826)) (countLit q [-1, -3, -6, -8, -9, -10, -15]) (countLit q [-16, -17, -20, -24, -26, -27, -30]) (count821 q) 2 4 (meaning795 q) (meaning817 q) (meaning826 q) hs
  change valuationOf q 795 = false ∨ valuationOf q 817 = false ∨ valuationOf q 826 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause536 (q : Snake 81) (h : Conditions q) : valuation q 795 = false ∨ valuation q 817 = false ∨ valuation q 826 = true := counterClause536 (baseVal q)

theorem counterClause537 (q : Nat → Bool) : valuationOf q 796 = false ∨ valuationOf q 823 = true := by
  have hs : count821 q = (countLit q [-1, -3, -6, -8, -9, -10, -15]) + (countLit q [-16, -17, -20, -24, -26, -27, -30]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -6, -8, -9, -10, -15]) (l₂ := [-16, -17, -20, -24, -26, -27, -30])
  have hm := merge_left (literal (valuationOf q) (796)) (literal (valuationOf q) (823)) (countLit q [-1, -3, -6, -8, -9, -10, -15]) (countLit q [-16, -17, -20, -24, -26, -27, -30]) (count821 q) 3 (meaning796 q) (meaning823 q) hs
  change valuationOf q 796 = false ∨ valuationOf q 823 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause537 (q : Snake 81) (h : Conditions q) : valuation q 796 = false ∨ valuation q 823 = true := counterClause537 (baseVal q)

theorem counterClause538 (q : Nat → Bool) : valuationOf q 796 = false ∨ valuationOf q 814 = false ∨ valuationOf q 824 = true := by
  have hs : count821 q = (countLit q [-1, -3, -6, -8, -9, -10, -15]) + (countLit q [-16, -17, -20, -24, -26, -27, -30]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -6, -8, -9, -10, -15]) (l₂ := [-16, -17, -20, -24, -26, -27, -30])
  have hm := merge_two (literal (valuationOf q) (796)) (literal (valuationOf q) (814)) (literal (valuationOf q) (824)) (countLit q [-1, -3, -6, -8, -9, -10, -15]) (countLit q [-16, -17, -20, -24, -26, -27, -30]) (count821 q) 3 1 (meaning796 q) (meaning814 q) (meaning824 q) hs
  change valuationOf q 796 = false ∨ valuationOf q 814 = false ∨ valuationOf q 824 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause538 (q : Snake 81) (h : Conditions q) : valuation q 796 = false ∨ valuation q 814 = false ∨ valuation q 824 = true := counterClause538 (baseVal q)

theorem counterClause539 (q : Nat → Bool) : valuationOf q 796 = false ∨ valuationOf q 815 = false ∨ valuationOf q 825 = true := by
  have hs : count821 q = (countLit q [-1, -3, -6, -8, -9, -10, -15]) + (countLit q [-16, -17, -20, -24, -26, -27, -30]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -6, -8, -9, -10, -15]) (l₂ := [-16, -17, -20, -24, -26, -27, -30])
  have hm := merge_two (literal (valuationOf q) (796)) (literal (valuationOf q) (815)) (literal (valuationOf q) (825)) (countLit q [-1, -3, -6, -8, -9, -10, -15]) (countLit q [-16, -17, -20, -24, -26, -27, -30]) (count821 q) 3 2 (meaning796 q) (meaning815 q) (meaning825 q) hs
  change valuationOf q 796 = false ∨ valuationOf q 815 = false ∨ valuationOf q 825 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause539 (q : Snake 81) (h : Conditions q) : valuation q 796 = false ∨ valuation q 815 = false ∨ valuation q 825 = true := counterClause539 (baseVal q)

theorem counterClause540 (q : Nat → Bool) : valuationOf q 796 = false ∨ valuationOf q 816 = false ∨ valuationOf q 826 = true := by
  have hs : count821 q = (countLit q [-1, -3, -6, -8, -9, -10, -15]) + (countLit q [-16, -17, -20, -24, -26, -27, -30]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -6, -8, -9, -10, -15]) (l₂ := [-16, -17, -20, -24, -26, -27, -30])
  have hm := merge_two (literal (valuationOf q) (796)) (literal (valuationOf q) (816)) (literal (valuationOf q) (826)) (countLit q [-1, -3, -6, -8, -9, -10, -15]) (countLit q [-16, -17, -20, -24, -26, -27, -30]) (count821 q) 3 3 (meaning796 q) (meaning816 q) (meaning826 q) hs
  change valuationOf q 796 = false ∨ valuationOf q 816 = false ∨ valuationOf q 826 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause540 (q : Snake 81) (h : Conditions q) : valuation q 796 = false ∨ valuation q 816 = false ∨ valuation q 826 = true := counterClause540 (baseVal q)

theorem counterClause541 (q : Nat → Bool) : valuationOf q 797 = false ∨ valuationOf q 814 = false ∨ valuationOf q 825 = true := by
  have hs : count821 q = (countLit q [-1, -3, -6, -8, -9, -10, -15]) + (countLit q [-16, -17, -20, -24, -26, -27, -30]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -6, -8, -9, -10, -15]) (l₂ := [-16, -17, -20, -24, -26, -27, -30])
  have hm := merge_two (literal (valuationOf q) (797)) (literal (valuationOf q) (814)) (literal (valuationOf q) (825)) (countLit q [-1, -3, -6, -8, -9, -10, -15]) (countLit q [-16, -17, -20, -24, -26, -27, -30]) (count821 q) 4 1 (meaning797 q) (meaning814 q) (meaning825 q) hs
  change valuationOf q 797 = false ∨ valuationOf q 814 = false ∨ valuationOf q 825 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause541 (q : Snake 81) (h : Conditions q) : valuation q 797 = false ∨ valuation q 814 = false ∨ valuation q 825 = true := counterClause541 (baseVal q)

theorem counterClause542 (q : Nat → Bool) : valuationOf q 797 = false ∨ valuationOf q 815 = false ∨ valuationOf q 826 = true := by
  have hs : count821 q = (countLit q [-1, -3, -6, -8, -9, -10, -15]) + (countLit q [-16, -17, -20, -24, -26, -27, -30]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -6, -8, -9, -10, -15]) (l₂ := [-16, -17, -20, -24, -26, -27, -30])
  have hm := merge_two (literal (valuationOf q) (797)) (literal (valuationOf q) (815)) (literal (valuationOf q) (826)) (countLit q [-1, -3, -6, -8, -9, -10, -15]) (countLit q [-16, -17, -20, -24, -26, -27, -30]) (count821 q) 4 2 (meaning797 q) (meaning815 q) (meaning826 q) hs
  change valuationOf q 797 = false ∨ valuationOf q 815 = false ∨ valuationOf q 826 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause542 (q : Snake 81) (h : Conditions q) : valuation q 797 = false ∨ valuation q 815 = false ∨ valuation q 826 = true := counterClause542 (baseVal q)

theorem counterClause543 (q : Nat → Bool) : valuationOf q 34 = true ∨ valuationOf q 835 = true := by
  have hs : count835 q = (countLit q [-32]) + (countLit q [-34]) := List.countP_append (p := literal q) (l₁ := [-32]) (l₂ := [-34])
  have hm := merge_right (literal (valuationOf q) (-34)) (literal (valuationOf q) (835)) (countLit q [-32]) (countLit q [-34]) (count835 q) 1 (meaningNeg34 q) (meaning835 q) hs
  change (! (valuationOf q 34)) = false ∨ valuationOf q 835 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause543 (q : Snake 81) (h : Conditions q) : valuation q 34 = true ∨ valuation q 835 = true := counterClause543 (baseVal q)

theorem counterClause544 (q : Nat → Bool) : valuationOf q 32 = true ∨ valuationOf q 835 = true := by
  have hs : count835 q = (countLit q [-32]) + (countLit q [-34]) := List.countP_append (p := literal q) (l₁ := [-32]) (l₂ := [-34])
  have hm := merge_left (literal (valuationOf q) (-32)) (literal (valuationOf q) (835)) (countLit q [-32]) (countLit q [-34]) (count835 q) 1 (meaningNeg32 q) (meaning835 q) hs
  change (! (valuationOf q 32)) = false ∨ valuationOf q 835 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause544 (q : Snake 81) (h : Conditions q) : valuation q 32 = true ∨ valuation q 835 = true := counterClause544 (baseVal q)

theorem block16 (q : Snake 81) (h : Conditions q) : B112E051.Block16 (valuation q) :=
  ⟨clause513 q h, clause514 q h, clause515 q h, clause516 q h, clause517 q h, clause518 q h, clause519 q h, clause520 q h, clause521 q h, clause522 q h, clause523 q h, clause524 q h, clause525 q h, clause526 q h, clause527 q h, clause528 q h, clause529 q h, clause530 q h, clause531 q h, clause532 q h, clause533 q h, clause534 q h, clause535 q h, clause536 q h, clause537 q h, clause538 q h, clause539 q h, clause540 q h, clause541 q h, clause542 q h, clause543 q h, clause544 q h⟩

end
end Snake9.Regrowth.E112051
