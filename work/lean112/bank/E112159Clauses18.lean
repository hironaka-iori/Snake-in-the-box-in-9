import E112159Semantics
import B112E159Inputs
namespace Snake9.Regrowth.E112159
noncomputable section
local instance blockDec18 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause577 (q : Nat → Bool) : valuationOf q 808 = false ∨ valuationOf q 810 = true := by
  have hs : count810 q = (countLit q [-5, -7]) + (countLit q [-9, -10]) := List.countP_append (p := literal q) (l₁ := [-5, -7]) (l₂ := [-9, -10])
  have hm := merge_right (literal (valuationOf q) (808)) (literal (valuationOf q) (810)) (countLit q [-5, -7]) (countLit q [-9, -10]) (count810 q) 1 (meaning808 q) (meaning810 q) hs
  change valuationOf q 808 = false ∨ valuationOf q 810 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause577 (q : Snake 81) (h : Conditions q) : valuation q 808 = false ∨ valuation q 810 = true := counterClause577 (baseVal q)

theorem counterClause578 (q : Nat → Bool) : valuationOf q 809 = false ∨ valuationOf q 811 = true := by
  have hs : count810 q = (countLit q [-5, -7]) + (countLit q [-9, -10]) := List.countP_append (p := literal q) (l₁ := [-5, -7]) (l₂ := [-9, -10])
  have hm := merge_right (literal (valuationOf q) (809)) (literal (valuationOf q) (811)) (countLit q [-5, -7]) (countLit q [-9, -10]) (count810 q) 2 (meaning809 q) (meaning811 q) hs
  change valuationOf q 809 = false ∨ valuationOf q 811 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause578 (q : Snake 81) (h : Conditions q) : valuation q 809 = false ∨ valuation q 811 = true := counterClause578 (baseVal q)

theorem counterClause579 (q : Nat → Bool) : valuationOf q 806 = false ∨ valuationOf q 808 = false ∨ valuationOf q 811 = true := by
  have hs : count810 q = (countLit q [-5, -7]) + (countLit q [-9, -10]) := List.countP_append (p := literal q) (l₁ := [-5, -7]) (l₂ := [-9, -10])
  have hm := merge_two (literal (valuationOf q) (806)) (literal (valuationOf q) (808)) (literal (valuationOf q) (811)) (countLit q [-5, -7]) (countLit q [-9, -10]) (count810 q) 1 1 (meaning806 q) (meaning808 q) (meaning811 q) hs
  change valuationOf q 806 = false ∨ valuationOf q 808 = false ∨ valuationOf q 811 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause579 (q : Snake 81) (h : Conditions q) : valuation q 806 = false ∨ valuation q 808 = false ∨ valuation q 811 = true := counterClause579 (baseVal q)

theorem counterClause580 (q : Nat → Bool) : valuationOf q 803 = false ∨ valuationOf q 814 = true := by
  have hs : count814 q = (countLit q [-1, -3, -4]) + (countLit q [-5, -7, -9, -10]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -4]) (l₂ := [-5, -7, -9, -10])
  have hm := merge_left (literal (valuationOf q) (803)) (literal (valuationOf q) (814)) (countLit q [-1, -3, -4]) (countLit q [-5, -7, -9, -10]) (count814 q) 1 (meaning803 q) (meaning814 q) hs
  change valuationOf q 803 = false ∨ valuationOf q 814 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause580 (q : Snake 81) (h : Conditions q) : valuation q 803 = false ∨ valuation q 814 = true := counterClause580 (baseVal q)

theorem counterClause581 (q : Nat → Bool) : valuationOf q 803 = false ∨ valuationOf q 810 = false ∨ valuationOf q 815 = true := by
  have hs : count814 q = (countLit q [-1, -3, -4]) + (countLit q [-5, -7, -9, -10]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -4]) (l₂ := [-5, -7, -9, -10])
  have hm := merge_two (literal (valuationOf q) (803)) (literal (valuationOf q) (810)) (literal (valuationOf q) (815)) (countLit q [-1, -3, -4]) (countLit q [-5, -7, -9, -10]) (count814 q) 1 1 (meaning803 q) (meaning810 q) (meaning815 q) hs
  change valuationOf q 803 = false ∨ valuationOf q 810 = false ∨ valuationOf q 815 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause581 (q : Snake 81) (h : Conditions q) : valuation q 803 = false ∨ valuation q 810 = false ∨ valuation q 815 = true := counterClause581 (baseVal q)

theorem counterClause582 (q : Nat → Bool) : valuationOf q 803 = false ∨ valuationOf q 811 = false ∨ valuationOf q 816 = true := by
  have hs : count814 q = (countLit q [-1, -3, -4]) + (countLit q [-5, -7, -9, -10]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -4]) (l₂ := [-5, -7, -9, -10])
  have hm := merge_two (literal (valuationOf q) (803)) (literal (valuationOf q) (811)) (literal (valuationOf q) (816)) (countLit q [-1, -3, -4]) (countLit q [-5, -7, -9, -10]) (count814 q) 1 2 (meaning803 q) (meaning811 q) (meaning816 q) hs
  change valuationOf q 803 = false ∨ valuationOf q 811 = false ∨ valuationOf q 816 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause582 (q : Snake 81) (h : Conditions q) : valuation q 803 = false ∨ valuation q 811 = false ∨ valuation q 816 = true := counterClause582 (baseVal q)

theorem counterClause583 (q : Nat → Bool) : valuationOf q 804 = false ∨ valuationOf q 810 = false ∨ valuationOf q 816 = true := by
  have hs : count814 q = (countLit q [-1, -3, -4]) + (countLit q [-5, -7, -9, -10]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -4]) (l₂ := [-5, -7, -9, -10])
  have hm := merge_two (literal (valuationOf q) (804)) (literal (valuationOf q) (810)) (literal (valuationOf q) (816)) (countLit q [-1, -3, -4]) (countLit q [-5, -7, -9, -10]) (count814 q) 2 1 (meaning804 q) (meaning810 q) (meaning816 q) hs
  change valuationOf q 804 = false ∨ valuationOf q 810 = false ∨ valuationOf q 816 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause583 (q : Snake 81) (h : Conditions q) : valuation q 804 = false ∨ valuation q 810 = false ∨ valuation q 816 = true := counterClause583 (baseVal q)

theorem counterClause584 (q : Nat → Bool) : valuationOf q 804 = false ∨ valuationOf q 811 = false ∨ valuationOf q 817 = true := by
  have hs : count814 q = (countLit q [-1, -3, -4]) + (countLit q [-5, -7, -9, -10]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -4]) (l₂ := [-5, -7, -9, -10])
  have hm := merge_two (literal (valuationOf q) (804)) (literal (valuationOf q) (811)) (literal (valuationOf q) (817)) (countLit q [-1, -3, -4]) (countLit q [-5, -7, -9, -10]) (count814 q) 2 2 (meaning804 q) (meaning811 q) (meaning817 q) hs
  change valuationOf q 804 = false ∨ valuationOf q 811 = false ∨ valuationOf q 817 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause584 (q : Snake 81) (h : Conditions q) : valuation q 804 = false ∨ valuation q 811 = false ∨ valuation q 817 = true := counterClause584 (baseVal q)

theorem counterClause585 (q : Nat → Bool) : valuationOf q 805 = false ∨ valuationOf q 810 = false ∨ valuationOf q 817 = true := by
  have hs : count814 q = (countLit q [-1, -3, -4]) + (countLit q [-5, -7, -9, -10]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -4]) (l₂ := [-5, -7, -9, -10])
  have hm := merge_two (literal (valuationOf q) (805)) (literal (valuationOf q) (810)) (literal (valuationOf q) (817)) (countLit q [-1, -3, -4]) (countLit q [-5, -7, -9, -10]) (count814 q) 3 1 (meaning805 q) (meaning810 q) (meaning817 q) hs
  change valuationOf q 805 = false ∨ valuationOf q 810 = false ∨ valuationOf q 817 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause585 (q : Snake 81) (h : Conditions q) : valuation q 805 = false ∨ valuation q 810 = false ∨ valuation q 817 = true := counterClause585 (baseVal q)

theorem counterClause586 (q : Nat → Bool) : valuationOf q 805 = false ∨ valuationOf q 811 = false ∨ valuationOf q 818 = true := by
  have hs : count814 q = (countLit q [-1, -3, -4]) + (countLit q [-5, -7, -9, -10]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -4]) (l₂ := [-5, -7, -9, -10])
  have hm := merge_two (literal (valuationOf q) (805)) (literal (valuationOf q) (811)) (literal (valuationOf q) (818)) (countLit q [-1, -3, -4]) (countLit q [-5, -7, -9, -10]) (count814 q) 3 2 (meaning805 q) (meaning811 q) (meaning818 q) hs
  change valuationOf q 805 = false ∨ valuationOf q 811 = false ∨ valuationOf q 818 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause586 (q : Snake 81) (h : Conditions q) : valuation q 805 = false ∨ valuation q 811 = false ∨ valuation q 818 = true := counterClause586 (baseVal q)

theorem counterClause587 (q : Nat → Bool) : valuationOf q 15 = true ∨ valuationOf q 821 = true := by
  have hs : count821 q = (countLit q [-14]) + (countLit q [-15]) := List.countP_append (p := literal q) (l₁ := [-14]) (l₂ := [-15])
  have hm := merge_right (literal (valuationOf q) (-15)) (literal (valuationOf q) (821)) (countLit q [-14]) (countLit q [-15]) (count821 q) 1 (meaningNeg15 q) (meaning821 q) hs
  change (! (valuationOf q 15)) = false ∨ valuationOf q 821 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause587 (q : Snake 81) (h : Conditions q) : valuation q 15 = true ∨ valuation q 821 = true := counterClause587 (baseVal q)

theorem counterClause588 (q : Nat → Bool) : valuationOf q 14 = true ∨ valuationOf q 821 = true := by
  have hs : count821 q = (countLit q [-14]) + (countLit q [-15]) := List.countP_append (p := literal q) (l₁ := [-14]) (l₂ := [-15])
  have hm := merge_left (literal (valuationOf q) (-14)) (literal (valuationOf q) (821)) (countLit q [-14]) (countLit q [-15]) (count821 q) 1 (meaningNeg14 q) (meaning821 q) hs
  change (! (valuationOf q 14)) = false ∨ valuationOf q 821 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause588 (q : Snake 81) (h : Conditions q) : valuation q 14 = true ∨ valuation q 821 = true := counterClause588 (baseVal q)

theorem counterClause589 (q : Nat → Bool) : valuationOf q 14 = true ∨ valuationOf q 15 = true ∨ valuationOf q 822 = true := by
  have hs : count821 q = (countLit q [-14]) + (countLit q [-15]) := List.countP_append (p := literal q) (l₁ := [-14]) (l₂ := [-15])
  have hm := merge_two (literal (valuationOf q) (-14)) (literal (valuationOf q) (-15)) (literal (valuationOf q) (822)) (countLit q [-14]) (countLit q [-15]) (count821 q) 1 1 (meaningNeg14 q) (meaningNeg15 q) (meaning822 q) hs
  change (! (valuationOf q 14)) = false ∨ (! (valuationOf q 15)) = false ∨ valuationOf q 822 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause589 (q : Snake 81) (h : Conditions q) : valuation q 14 = true ∨ valuation q 15 = true ∨ valuation q 822 = true := counterClause589 (baseVal q)

theorem counterClause590 (q : Nat → Bool) : valuationOf q 821 = false ∨ valuationOf q 823 = true := by
  have hs : count823 q = (countLit q [-12]) + (countLit q [-14, -15]) := List.countP_append (p := literal q) (l₁ := [-12]) (l₂ := [-14, -15])
  have hm := merge_right (literal (valuationOf q) (821)) (literal (valuationOf q) (823)) (countLit q [-12]) (countLit q [-14, -15]) (count823 q) 1 (meaning821 q) (meaning823 q) hs
  change valuationOf q 821 = false ∨ valuationOf q 823 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause590 (q : Snake 81) (h : Conditions q) : valuation q 821 = false ∨ valuation q 823 = true := counterClause590 (baseVal q)

theorem counterClause591 (q : Nat → Bool) : valuationOf q 822 = false ∨ valuationOf q 824 = true := by
  have hs : count823 q = (countLit q [-12]) + (countLit q [-14, -15]) := List.countP_append (p := literal q) (l₁ := [-12]) (l₂ := [-14, -15])
  have hm := merge_right (literal (valuationOf q) (822)) (literal (valuationOf q) (824)) (countLit q [-12]) (countLit q [-14, -15]) (count823 q) 2 (meaning822 q) (meaning824 q) hs
  change valuationOf q 822 = false ∨ valuationOf q 824 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause591 (q : Snake 81) (h : Conditions q) : valuation q 822 = false ∨ valuation q 824 = true := counterClause591 (baseVal q)

theorem counterClause592 (q : Nat → Bool) : valuationOf q 12 = true ∨ valuationOf q 823 = true := by
  have hs : count823 q = (countLit q [-12]) + (countLit q [-14, -15]) := List.countP_append (p := literal q) (l₁ := [-12]) (l₂ := [-14, -15])
  have hm := merge_left (literal (valuationOf q) (-12)) (literal (valuationOf q) (823)) (countLit q [-12]) (countLit q [-14, -15]) (count823 q) 1 (meaningNeg12 q) (meaning823 q) hs
  change (! (valuationOf q 12)) = false ∨ valuationOf q 823 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause592 (q : Snake 81) (h : Conditions q) : valuation q 12 = true ∨ valuation q 823 = true := counterClause592 (baseVal q)

theorem counterClause593 (q : Nat → Bool) : valuationOf q 12 = true ∨ valuationOf q 821 = false ∨ valuationOf q 824 = true := by
  have hs : count823 q = (countLit q [-12]) + (countLit q [-14, -15]) := List.countP_append (p := literal q) (l₁ := [-12]) (l₂ := [-14, -15])
  have hm := merge_two (literal (valuationOf q) (-12)) (literal (valuationOf q) (821)) (literal (valuationOf q) (824)) (countLit q [-12]) (countLit q [-14, -15]) (count823 q) 1 1 (meaningNeg12 q) (meaning821 q) (meaning824 q) hs
  change (! (valuationOf q 12)) = false ∨ valuationOf q 821 = false ∨ valuationOf q 824 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause593 (q : Snake 81) (h : Conditions q) : valuation q 12 = true ∨ valuation q 821 = false ∨ valuation q 824 = true := counterClause593 (baseVal q)

theorem counterClause594 (q : Nat → Bool) : valuationOf q 12 = true ∨ valuationOf q 822 = false ∨ valuationOf q 825 = true := by
  have hs : count823 q = (countLit q [-12]) + (countLit q [-14, -15]) := List.countP_append (p := literal q) (l₁ := [-12]) (l₂ := [-14, -15])
  have hm := merge_two (literal (valuationOf q) (-12)) (literal (valuationOf q) (822)) (literal (valuationOf q) (825)) (countLit q [-12]) (countLit q [-14, -15]) (count823 q) 1 2 (meaningNeg12 q) (meaning822 q) (meaning825 q) hs
  change (! (valuationOf q 12)) = false ∨ valuationOf q 822 = false ∨ valuationOf q 825 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause594 (q : Snake 81) (h : Conditions q) : valuation q 12 = true ∨ valuation q 822 = false ∨ valuation q 825 = true := counterClause594 (baseVal q)

theorem counterClause595 (q : Nat → Bool) : valuationOf q 21 = true ∨ valuationOf q 826 = true := by
  have hs : count826 q = (countLit q [-18]) + (countLit q [-21]) := List.countP_append (p := literal q) (l₁ := [-18]) (l₂ := [-21])
  have hm := merge_right (literal (valuationOf q) (-21)) (literal (valuationOf q) (826)) (countLit q [-18]) (countLit q [-21]) (count826 q) 1 (meaningNeg21 q) (meaning826 q) hs
  change (! (valuationOf q 21)) = false ∨ valuationOf q 826 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause595 (q : Snake 81) (h : Conditions q) : valuation q 21 = true ∨ valuation q 826 = true := counterClause595 (baseVal q)

theorem counterClause596 (q : Nat → Bool) : valuationOf q 18 = true ∨ valuationOf q 826 = true := by
  have hs : count826 q = (countLit q [-18]) + (countLit q [-21]) := List.countP_append (p := literal q) (l₁ := [-18]) (l₂ := [-21])
  have hm := merge_left (literal (valuationOf q) (-18)) (literal (valuationOf q) (826)) (countLit q [-18]) (countLit q [-21]) (count826 q) 1 (meaningNeg18 q) (meaning826 q) hs
  change (! (valuationOf q 18)) = false ∨ valuationOf q 826 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause596 (q : Snake 81) (h : Conditions q) : valuation q 18 = true ∨ valuation q 826 = true := counterClause596 (baseVal q)

theorem counterClause597 (q : Nat → Bool) : valuationOf q 18 = true ∨ valuationOf q 21 = true ∨ valuationOf q 827 = true := by
  have hs : count826 q = (countLit q [-18]) + (countLit q [-21]) := List.countP_append (p := literal q) (l₁ := [-18]) (l₂ := [-21])
  have hm := merge_two (literal (valuationOf q) (-18)) (literal (valuationOf q) (-21)) (literal (valuationOf q) (827)) (countLit q [-18]) (countLit q [-21]) (count826 q) 1 1 (meaningNeg18 q) (meaningNeg21 q) (meaning827 q) hs
  change (! (valuationOf q 18)) = false ∨ (! (valuationOf q 21)) = false ∨ valuationOf q 827 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause597 (q : Snake 81) (h : Conditions q) : valuation q 18 = true ∨ valuation q 21 = true ∨ valuation q 827 = true := counterClause597 (baseVal q)

theorem counterClause598 (q : Nat → Bool) : valuationOf q 24 = true ∨ valuationOf q 828 = true := by
  have hs : count828 q = (countLit q [-23]) + (countLit q [-24]) := List.countP_append (p := literal q) (l₁ := [-23]) (l₂ := [-24])
  have hm := merge_right (literal (valuationOf q) (-24)) (literal (valuationOf q) (828)) (countLit q [-23]) (countLit q [-24]) (count828 q) 1 (meaningNeg24 q) (meaning828 q) hs
  change (! (valuationOf q 24)) = false ∨ valuationOf q 828 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause598 (q : Snake 81) (h : Conditions q) : valuation q 24 = true ∨ valuation q 828 = true := counterClause598 (baseVal q)

theorem counterClause599 (q : Nat → Bool) : valuationOf q 23 = true ∨ valuationOf q 828 = true := by
  have hs : count828 q = (countLit q [-23]) + (countLit q [-24]) := List.countP_append (p := literal q) (l₁ := [-23]) (l₂ := [-24])
  have hm := merge_left (literal (valuationOf q) (-23)) (literal (valuationOf q) (828)) (countLit q [-23]) (countLit q [-24]) (count828 q) 1 (meaningNeg23 q) (meaning828 q) hs
  change (! (valuationOf q 23)) = false ∨ valuationOf q 828 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause599 (q : Snake 81) (h : Conditions q) : valuation q 23 = true ∨ valuation q 828 = true := counterClause599 (baseVal q)

theorem counterClause600 (q : Nat → Bool) : valuationOf q 23 = true ∨ valuationOf q 24 = true ∨ valuationOf q 829 = true := by
  have hs : count828 q = (countLit q [-23]) + (countLit q [-24]) := List.countP_append (p := literal q) (l₁ := [-23]) (l₂ := [-24])
  have hm := merge_two (literal (valuationOf q) (-23)) (literal (valuationOf q) (-24)) (literal (valuationOf q) (829)) (countLit q [-23]) (countLit q [-24]) (count828 q) 1 1 (meaningNeg23 q) (meaningNeg24 q) (meaning829 q) hs
  change (! (valuationOf q 23)) = false ∨ (! (valuationOf q 24)) = false ∨ valuationOf q 829 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause600 (q : Snake 81) (h : Conditions q) : valuation q 23 = true ∨ valuation q 24 = true ∨ valuation q 829 = true := counterClause600 (baseVal q)

theorem counterClause601 (q : Nat → Bool) : valuationOf q 828 = false ∨ valuationOf q 830 = true := by
  have hs : count830 q = (countLit q [-18, -21]) + (countLit q [-23, -24]) := List.countP_append (p := literal q) (l₁ := [-18, -21]) (l₂ := [-23, -24])
  have hm := merge_right (literal (valuationOf q) (828)) (literal (valuationOf q) (830)) (countLit q [-18, -21]) (countLit q [-23, -24]) (count830 q) 1 (meaning828 q) (meaning830 q) hs
  change valuationOf q 828 = false ∨ valuationOf q 830 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause601 (q : Snake 81) (h : Conditions q) : valuation q 828 = false ∨ valuation q 830 = true := counterClause601 (baseVal q)

theorem counterClause602 (q : Nat → Bool) : valuationOf q 829 = false ∨ valuationOf q 831 = true := by
  have hs : count830 q = (countLit q [-18, -21]) + (countLit q [-23, -24]) := List.countP_append (p := literal q) (l₁ := [-18, -21]) (l₂ := [-23, -24])
  have hm := merge_right (literal (valuationOf q) (829)) (literal (valuationOf q) (831)) (countLit q [-18, -21]) (countLit q [-23, -24]) (count830 q) 2 (meaning829 q) (meaning831 q) hs
  change valuationOf q 829 = false ∨ valuationOf q 831 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause602 (q : Snake 81) (h : Conditions q) : valuation q 829 = false ∨ valuation q 831 = true := counterClause602 (baseVal q)

theorem counterClause603 (q : Nat → Bool) : valuationOf q 826 = false ∨ valuationOf q 830 = true := by
  have hs : count830 q = (countLit q [-18, -21]) + (countLit q [-23, -24]) := List.countP_append (p := literal q) (l₁ := [-18, -21]) (l₂ := [-23, -24])
  have hm := merge_left (literal (valuationOf q) (826)) (literal (valuationOf q) (830)) (countLit q [-18, -21]) (countLit q [-23, -24]) (count830 q) 1 (meaning826 q) (meaning830 q) hs
  change valuationOf q 826 = false ∨ valuationOf q 830 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause603 (q : Snake 81) (h : Conditions q) : valuation q 826 = false ∨ valuation q 830 = true := counterClause603 (baseVal q)

theorem counterClause604 (q : Nat → Bool) : valuationOf q 826 = false ∨ valuationOf q 828 = false ∨ valuationOf q 831 = true := by
  have hs : count830 q = (countLit q [-18, -21]) + (countLit q [-23, -24]) := List.countP_append (p := literal q) (l₁ := [-18, -21]) (l₂ := [-23, -24])
  have hm := merge_two (literal (valuationOf q) (826)) (literal (valuationOf q) (828)) (literal (valuationOf q) (831)) (countLit q [-18, -21]) (countLit q [-23, -24]) (count830 q) 1 1 (meaning826 q) (meaning828 q) (meaning831 q) hs
  change valuationOf q 826 = false ∨ valuationOf q 828 = false ∨ valuationOf q 831 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause604 (q : Snake 81) (h : Conditions q) : valuation q 826 = false ∨ valuation q 828 = false ∨ valuation q 831 = true := counterClause604 (baseVal q)

theorem counterClause605 (q : Nat → Bool) : valuationOf q 826 = false ∨ valuationOf q 829 = false ∨ valuationOf q 832 = true := by
  have hs : count830 q = (countLit q [-18, -21]) + (countLit q [-23, -24]) := List.countP_append (p := literal q) (l₁ := [-18, -21]) (l₂ := [-23, -24])
  have hm := merge_two (literal (valuationOf q) (826)) (literal (valuationOf q) (829)) (literal (valuationOf q) (832)) (countLit q [-18, -21]) (countLit q [-23, -24]) (count830 q) 1 2 (meaning826 q) (meaning829 q) (meaning832 q) hs
  change valuationOf q 826 = false ∨ valuationOf q 829 = false ∨ valuationOf q 832 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause605 (q : Snake 81) (h : Conditions q) : valuation q 826 = false ∨ valuation q 829 = false ∨ valuation q 832 = true := counterClause605 (baseVal q)

theorem counterClause606 (q : Nat → Bool) : valuationOf q 827 = false ∨ valuationOf q 831 = true := by
  have hs : count830 q = (countLit q [-18, -21]) + (countLit q [-23, -24]) := List.countP_append (p := literal q) (l₁ := [-18, -21]) (l₂ := [-23, -24])
  have hm := merge_left (literal (valuationOf q) (827)) (literal (valuationOf q) (831)) (countLit q [-18, -21]) (countLit q [-23, -24]) (count830 q) 2 (meaning827 q) (meaning831 q) hs
  change valuationOf q 827 = false ∨ valuationOf q 831 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause606 (q : Snake 81) (h : Conditions q) : valuation q 827 = false ∨ valuation q 831 = true := counterClause606 (baseVal q)

theorem counterClause607 (q : Nat → Bool) : valuationOf q 827 = false ∨ valuationOf q 828 = false ∨ valuationOf q 832 = true := by
  have hs : count830 q = (countLit q [-18, -21]) + (countLit q [-23, -24]) := List.countP_append (p := literal q) (l₁ := [-18, -21]) (l₂ := [-23, -24])
  have hm := merge_two (literal (valuationOf q) (827)) (literal (valuationOf q) (828)) (literal (valuationOf q) (832)) (countLit q [-18, -21]) (countLit q [-23, -24]) (count830 q) 2 1 (meaning827 q) (meaning828 q) (meaning832 q) hs
  change valuationOf q 827 = false ∨ valuationOf q 828 = false ∨ valuationOf q 832 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause607 (q : Snake 81) (h : Conditions q) : valuation q 827 = false ∨ valuation q 828 = false ∨ valuation q 832 = true := counterClause607 (baseVal q)

theorem counterClause608 (q : Nat → Bool) : valuationOf q 827 = false ∨ valuationOf q 829 = false ∨ valuationOf q 833 = true := by
  have hs : count830 q = (countLit q [-18, -21]) + (countLit q [-23, -24]) := List.countP_append (p := literal q) (l₁ := [-18, -21]) (l₂ := [-23, -24])
  have hm := merge_two (literal (valuationOf q) (827)) (literal (valuationOf q) (829)) (literal (valuationOf q) (833)) (countLit q [-18, -21]) (countLit q [-23, -24]) (count830 q) 2 2 (meaning827 q) (meaning829 q) (meaning833 q) hs
  change valuationOf q 827 = false ∨ valuationOf q 829 = false ∨ valuationOf q 833 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause608 (q : Snake 81) (h : Conditions q) : valuation q 827 = false ∨ valuation q 829 = false ∨ valuation q 833 = true := counterClause608 (baseVal q)

theorem block18 (q : Snake 81) (h : Conditions q) : B112E159.Block18 (valuation q) :=
  ⟨clause577 q h, clause578 q h, clause579 q h, clause580 q h, clause581 q h, clause582 q h, clause583 q h, clause584 q h, clause585 q h, clause586 q h, clause587 q h, clause588 q h, clause589 q h, clause590 q h, clause591 q h, clause592 q h, clause593 q h, clause594 q h, clause595 q h, clause596 q h, clause597 q h, clause598 q h, clause599 q h, clause600 q h, clause601 q h, clause602 q h, clause603 q h, clause604 q h, clause605 q h, clause606 q h, clause607 q h, clause608 q h⟩

end
end Snake9.Regrowth.E112159
