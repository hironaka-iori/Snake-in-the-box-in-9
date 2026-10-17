import E112185Semantics
import B112E185Inputs
namespace Snake9.Regrowth.E112185
noncomputable section
local instance blockDec18 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause577 (q : Nat → Bool) : valuationOf q 811 = false ∨ valuationOf q 838 = true := by
  have hs : count837 q = (countLit q [-27, -29, -31, -32, -34, -37, -39]) + (countLit q [-40, -43, -45, -46, -48, -51, -53]) := List.countP_append (p := literal q) (l₁ := [-27, -29, -31, -32, -34, -37, -39]) (l₂ := [-40, -43, -45, -46, -48, -51, -53])
  have hm := merge_left (literal (valuationOf q) (811)) (literal (valuationOf q) (838)) (countLit q [-27, -29, -31, -32, -34, -37, -39]) (countLit q [-40, -43, -45, -46, -48, -51, -53]) (count837 q) 2 (meaning811 q) (meaning838 q) hs
  change valuationOf q 811 = false ∨ valuationOf q 838 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause577 (q : Snake 81) (h : Conditions q) : valuation q 811 = false ∨ valuation q 838 = true := counterClause577 (baseVal q)

theorem counterClause578 (q : Nat → Bool) : valuationOf q 811 = false ∨ valuationOf q 830 = false ∨ valuationOf q 839 = true := by
  have hs : count837 q = (countLit q [-27, -29, -31, -32, -34, -37, -39]) + (countLit q [-40, -43, -45, -46, -48, -51, -53]) := List.countP_append (p := literal q) (l₁ := [-27, -29, -31, -32, -34, -37, -39]) (l₂ := [-40, -43, -45, -46, -48, -51, -53])
  have hm := merge_two (literal (valuationOf q) (811)) (literal (valuationOf q) (830)) (literal (valuationOf q) (839)) (countLit q [-27, -29, -31, -32, -34, -37, -39]) (countLit q [-40, -43, -45, -46, -48, -51, -53]) (count837 q) 2 1 (meaning811 q) (meaning830 q) (meaning839 q) hs
  change valuationOf q 811 = false ∨ valuationOf q 830 = false ∨ valuationOf q 839 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause578 (q : Snake 81) (h : Conditions q) : valuation q 811 = false ∨ valuation q 830 = false ∨ valuation q 839 = true := counterClause578 (baseVal q)

theorem counterClause579 (q : Nat → Bool) : valuationOf q 811 = false ∨ valuationOf q 831 = false ∨ valuationOf q 840 = true := by
  have hs : count837 q = (countLit q [-27, -29, -31, -32, -34, -37, -39]) + (countLit q [-40, -43, -45, -46, -48, -51, -53]) := List.countP_append (p := literal q) (l₁ := [-27, -29, -31, -32, -34, -37, -39]) (l₂ := [-40, -43, -45, -46, -48, -51, -53])
  have hm := merge_two (literal (valuationOf q) (811)) (literal (valuationOf q) (831)) (literal (valuationOf q) (840)) (countLit q [-27, -29, -31, -32, -34, -37, -39]) (countLit q [-40, -43, -45, -46, -48, -51, -53]) (count837 q) 2 2 (meaning811 q) (meaning831 q) (meaning840 q) hs
  change valuationOf q 811 = false ∨ valuationOf q 831 = false ∨ valuationOf q 840 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause579 (q : Snake 81) (h : Conditions q) : valuation q 811 = false ∨ valuation q 831 = false ∨ valuation q 840 = true := counterClause579 (baseVal q)

theorem counterClause580 (q : Nat → Bool) : valuationOf q 811 = false ∨ valuationOf q 832 = false ∨ valuationOf q 841 = true := by
  have hs : count837 q = (countLit q [-27, -29, -31, -32, -34, -37, -39]) + (countLit q [-40, -43, -45, -46, -48, -51, -53]) := List.countP_append (p := literal q) (l₁ := [-27, -29, -31, -32, -34, -37, -39]) (l₂ := [-40, -43, -45, -46, -48, -51, -53])
  have hm := merge_two (literal (valuationOf q) (811)) (literal (valuationOf q) (832)) (literal (valuationOf q) (841)) (countLit q [-27, -29, -31, -32, -34, -37, -39]) (countLit q [-40, -43, -45, -46, -48, -51, -53]) (count837 q) 2 3 (meaning811 q) (meaning832 q) (meaning841 q) hs
  change valuationOf q 811 = false ∨ valuationOf q 832 = false ∨ valuationOf q 841 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause580 (q : Snake 81) (h : Conditions q) : valuation q 811 = false ∨ valuation q 832 = false ∨ valuation q 841 = true := counterClause580 (baseVal q)

theorem counterClause581 (q : Nat → Bool) : valuationOf q 812 = false ∨ valuationOf q 839 = true := by
  have hs : count837 q = (countLit q [-27, -29, -31, -32, -34, -37, -39]) + (countLit q [-40, -43, -45, -46, -48, -51, -53]) := List.countP_append (p := literal q) (l₁ := [-27, -29, -31, -32, -34, -37, -39]) (l₂ := [-40, -43, -45, -46, -48, -51, -53])
  have hm := merge_left (literal (valuationOf q) (812)) (literal (valuationOf q) (839)) (countLit q [-27, -29, -31, -32, -34, -37, -39]) (countLit q [-40, -43, -45, -46, -48, -51, -53]) (count837 q) 3 (meaning812 q) (meaning839 q) hs
  change valuationOf q 812 = false ∨ valuationOf q 839 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause581 (q : Snake 81) (h : Conditions q) : valuation q 812 = false ∨ valuation q 839 = true := counterClause581 (baseVal q)

theorem counterClause582 (q : Nat → Bool) : valuationOf q 812 = false ∨ valuationOf q 830 = false ∨ valuationOf q 840 = true := by
  have hs : count837 q = (countLit q [-27, -29, -31, -32, -34, -37, -39]) + (countLit q [-40, -43, -45, -46, -48, -51, -53]) := List.countP_append (p := literal q) (l₁ := [-27, -29, -31, -32, -34, -37, -39]) (l₂ := [-40, -43, -45, -46, -48, -51, -53])
  have hm := merge_two (literal (valuationOf q) (812)) (literal (valuationOf q) (830)) (literal (valuationOf q) (840)) (countLit q [-27, -29, -31, -32, -34, -37, -39]) (countLit q [-40, -43, -45, -46, -48, -51, -53]) (count837 q) 3 1 (meaning812 q) (meaning830 q) (meaning840 q) hs
  change valuationOf q 812 = false ∨ valuationOf q 830 = false ∨ valuationOf q 840 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause582 (q : Snake 81) (h : Conditions q) : valuation q 812 = false ∨ valuation q 830 = false ∨ valuation q 840 = true := counterClause582 (baseVal q)

theorem counterClause583 (q : Nat → Bool) : valuationOf q 812 = false ∨ valuationOf q 831 = false ∨ valuationOf q 841 = true := by
  have hs : count837 q = (countLit q [-27, -29, -31, -32, -34, -37, -39]) + (countLit q [-40, -43, -45, -46, -48, -51, -53]) := List.countP_append (p := literal q) (l₁ := [-27, -29, -31, -32, -34, -37, -39]) (l₂ := [-40, -43, -45, -46, -48, -51, -53])
  have hm := merge_two (literal (valuationOf q) (812)) (literal (valuationOf q) (831)) (literal (valuationOf q) (841)) (countLit q [-27, -29, -31, -32, -34, -37, -39]) (countLit q [-40, -43, -45, -46, -48, -51, -53]) (count837 q) 3 2 (meaning812 q) (meaning831 q) (meaning841 q) hs
  change valuationOf q 812 = false ∨ valuationOf q 831 = false ∨ valuationOf q 841 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause583 (q : Snake 81) (h : Conditions q) : valuation q 812 = false ∨ valuation q 831 = false ∨ valuation q 841 = true := counterClause583 (baseVal q)

theorem counterClause584 (q : Nat → Bool) : valuationOf q 812 = false ∨ valuationOf q 832 = false ∨ valuationOf q 842 = true := by
  have hs : count837 q = (countLit q [-27, -29, -31, -32, -34, -37, -39]) + (countLit q [-40, -43, -45, -46, -48, -51, -53]) := List.countP_append (p := literal q) (l₁ := [-27, -29, -31, -32, -34, -37, -39]) (l₂ := [-40, -43, -45, -46, -48, -51, -53])
  have hm := merge_two (literal (valuationOf q) (812)) (literal (valuationOf q) (832)) (literal (valuationOf q) (842)) (countLit q [-27, -29, -31, -32, -34, -37, -39]) (countLit q [-40, -43, -45, -46, -48, -51, -53]) (count837 q) 3 3 (meaning812 q) (meaning832 q) (meaning842 q) hs
  change valuationOf q 812 = false ∨ valuationOf q 832 = false ∨ valuationOf q 842 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause584 (q : Snake 81) (h : Conditions q) : valuation q 812 = false ∨ valuation q 832 = false ∨ valuation q 842 = true := counterClause584 (baseVal q)

theorem counterClause585 (q : Nat → Bool) : valuationOf q 813 = false ∨ valuationOf q 840 = true := by
  have hs : count837 q = (countLit q [-27, -29, -31, -32, -34, -37, -39]) + (countLit q [-40, -43, -45, -46, -48, -51, -53]) := List.countP_append (p := literal q) (l₁ := [-27, -29, -31, -32, -34, -37, -39]) (l₂ := [-40, -43, -45, -46, -48, -51, -53])
  have hm := merge_left (literal (valuationOf q) (813)) (literal (valuationOf q) (840)) (countLit q [-27, -29, -31, -32, -34, -37, -39]) (countLit q [-40, -43, -45, -46, -48, -51, -53]) (count837 q) 4 (meaning813 q) (meaning840 q) hs
  change valuationOf q 813 = false ∨ valuationOf q 840 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause585 (q : Snake 81) (h : Conditions q) : valuation q 813 = false ∨ valuation q 840 = true := counterClause585 (baseVal q)

theorem counterClause586 (q : Nat → Bool) : valuationOf q 813 = false ∨ valuationOf q 830 = false ∨ valuationOf q 841 = true := by
  have hs : count837 q = (countLit q [-27, -29, -31, -32, -34, -37, -39]) + (countLit q [-40, -43, -45, -46, -48, -51, -53]) := List.countP_append (p := literal q) (l₁ := [-27, -29, -31, -32, -34, -37, -39]) (l₂ := [-40, -43, -45, -46, -48, -51, -53])
  have hm := merge_two (literal (valuationOf q) (813)) (literal (valuationOf q) (830)) (literal (valuationOf q) (841)) (countLit q [-27, -29, -31, -32, -34, -37, -39]) (countLit q [-40, -43, -45, -46, -48, -51, -53]) (count837 q) 4 1 (meaning813 q) (meaning830 q) (meaning841 q) hs
  change valuationOf q 813 = false ∨ valuationOf q 830 = false ∨ valuationOf q 841 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause586 (q : Snake 81) (h : Conditions q) : valuation q 813 = false ∨ valuation q 830 = false ∨ valuation q 841 = true := counterClause586 (baseVal q)

theorem counterClause587 (q : Nat → Bool) : valuationOf q 814 = false ∨ valuationOf q 841 = true := by
  have hs : count837 q = (countLit q [-27, -29, -31, -32, -34, -37, -39]) + (countLit q [-40, -43, -45, -46, -48, -51, -53]) := List.countP_append (p := literal q) (l₁ := [-27, -29, -31, -32, -34, -37, -39]) (l₂ := [-40, -43, -45, -46, -48, -51, -53])
  have hm := merge_left (literal (valuationOf q) (814)) (literal (valuationOf q) (841)) (countLit q [-27, -29, -31, -32, -34, -37, -39]) (countLit q [-40, -43, -45, -46, -48, -51, -53]) (count837 q) 5 (meaning814 q) (meaning841 q) hs
  change valuationOf q 814 = false ∨ valuationOf q 841 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause587 (q : Snake 81) (h : Conditions q) : valuation q 814 = false ∨ valuation q 841 = true := counterClause587 (baseVal q)

theorem counterClause588 (q : Nat → Bool) : valuationOf q 786 = false ∨ valuationOf q 842 = false ∨ valuationOf q 860 = true := by
  have hs : count851 q = (countLit q [-1, -4, -5, -6, -9, -11, -12, -15, -17, -18, -20, -21, -24, -25]) + (countLit q [-27, -29, -31, -32, -34, -37, -39, -40, -43, -45, -46, -48, -51, -53]) := List.countP_append (p := literal q) (l₁ := [-1, -4, -5, -6, -9, -11, -12, -15, -17, -18, -20, -21, -24, -25]) (l₂ := [-27, -29, -31, -32, -34, -37, -39, -40, -43, -45, -46, -48, -51, -53])
  have hm := merge_two (literal (valuationOf q) (786)) (literal (valuationOf q) (842)) (literal (valuationOf q) (860)) (countLit q [-1, -4, -5, -6, -9, -11, -12, -15, -17, -18, -20, -21, -24, -25]) (countLit q [-27, -29, -31, -32, -34, -37, -39, -40, -43, -45, -46, -48, -51, -53]) (count851 q) 4 6 (meaning786 q) (meaning842 q) (meaning860 q) hs
  change valuationOf q 786 = false ∨ valuationOf q 842 = false ∨ valuationOf q 860 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause588 (q : Snake 81) (h : Conditions q) : valuation q 786 = false ∨ valuation q 842 = false ∨ valuation q 860 = true := counterClause588 (baseVal q)

theorem counterClause589 (q : Nat → Bool) : valuationOf q 787 = false ∨ valuationOf q 838 = false ∨ valuationOf q 857 = true := by
  have hs : count851 q = (countLit q [-1, -4, -5, -6, -9, -11, -12, -15, -17, -18, -20, -21, -24, -25]) + (countLit q [-27, -29, -31, -32, -34, -37, -39, -40, -43, -45, -46, -48, -51, -53]) := List.countP_append (p := literal q) (l₁ := [-1, -4, -5, -6, -9, -11, -12, -15, -17, -18, -20, -21, -24, -25]) (l₂ := [-27, -29, -31, -32, -34, -37, -39, -40, -43, -45, -46, -48, -51, -53])
  have hm := merge_two (literal (valuationOf q) (787)) (literal (valuationOf q) (838)) (literal (valuationOf q) (857)) (countLit q [-1, -4, -5, -6, -9, -11, -12, -15, -17, -18, -20, -21, -24, -25]) (countLit q [-27, -29, -31, -32, -34, -37, -39, -40, -43, -45, -46, -48, -51, -53]) (count851 q) 5 2 (meaning787 q) (meaning838 q) (meaning857 q) hs
  change valuationOf q 787 = false ∨ valuationOf q 838 = false ∨ valuationOf q 857 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause589 (q : Snake 81) (h : Conditions q) : valuation q 787 = false ∨ valuation q 838 = false ∨ valuation q 857 = true := counterClause589 (baseVal q)

theorem counterClause590 (q : Nat → Bool) : valuationOf q 787 = false ∨ valuationOf q 839 = false ∨ valuationOf q 858 = true := by
  have hs : count851 q = (countLit q [-1, -4, -5, -6, -9, -11, -12, -15, -17, -18, -20, -21, -24, -25]) + (countLit q [-27, -29, -31, -32, -34, -37, -39, -40, -43, -45, -46, -48, -51, -53]) := List.countP_append (p := literal q) (l₁ := [-1, -4, -5, -6, -9, -11, -12, -15, -17, -18, -20, -21, -24, -25]) (l₂ := [-27, -29, -31, -32, -34, -37, -39, -40, -43, -45, -46, -48, -51, -53])
  have hm := merge_two (literal (valuationOf q) (787)) (literal (valuationOf q) (839)) (literal (valuationOf q) (858)) (countLit q [-1, -4, -5, -6, -9, -11, -12, -15, -17, -18, -20, -21, -24, -25]) (countLit q [-27, -29, -31, -32, -34, -37, -39, -40, -43, -45, -46, -48, -51, -53]) (count851 q) 5 3 (meaning787 q) (meaning839 q) (meaning858 q) hs
  change valuationOf q 787 = false ∨ valuationOf q 839 = false ∨ valuationOf q 858 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause590 (q : Snake 81) (h : Conditions q) : valuation q 787 = false ∨ valuation q 839 = false ∨ valuation q 858 = true := counterClause590 (baseVal q)

theorem counterClause591 (q : Nat → Bool) : valuationOf q 787 = false ∨ valuationOf q 840 = false ∨ valuationOf q 859 = true := by
  have hs : count851 q = (countLit q [-1, -4, -5, -6, -9, -11, -12, -15, -17, -18, -20, -21, -24, -25]) + (countLit q [-27, -29, -31, -32, -34, -37, -39, -40, -43, -45, -46, -48, -51, -53]) := List.countP_append (p := literal q) (l₁ := [-1, -4, -5, -6, -9, -11, -12, -15, -17, -18, -20, -21, -24, -25]) (l₂ := [-27, -29, -31, -32, -34, -37, -39, -40, -43, -45, -46, -48, -51, -53])
  have hm := merge_two (literal (valuationOf q) (787)) (literal (valuationOf q) (840)) (literal (valuationOf q) (859)) (countLit q [-1, -4, -5, -6, -9, -11, -12, -15, -17, -18, -20, -21, -24, -25]) (countLit q [-27, -29, -31, -32, -34, -37, -39, -40, -43, -45, -46, -48, -51, -53]) (count851 q) 5 4 (meaning787 q) (meaning840 q) (meaning859 q) hs
  change valuationOf q 787 = false ∨ valuationOf q 840 = false ∨ valuationOf q 859 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause591 (q : Snake 81) (h : Conditions q) : valuation q 787 = false ∨ valuation q 840 = false ∨ valuation q 859 = true := counterClause591 (baseVal q)

theorem counterClause592 (q : Nat → Bool) : valuationOf q 788 = false ∨ valuationOf q 838 = false ∨ valuationOf q 858 = true := by
  have hs : count851 q = (countLit q [-1, -4, -5, -6, -9, -11, -12, -15, -17, -18, -20, -21, -24, -25]) + (countLit q [-27, -29, -31, -32, -34, -37, -39, -40, -43, -45, -46, -48, -51, -53]) := List.countP_append (p := literal q) (l₁ := [-1, -4, -5, -6, -9, -11, -12, -15, -17, -18, -20, -21, -24, -25]) (l₂ := [-27, -29, -31, -32, -34, -37, -39, -40, -43, -45, -46, -48, -51, -53])
  have hm := merge_two (literal (valuationOf q) (788)) (literal (valuationOf q) (838)) (literal (valuationOf q) (858)) (countLit q [-1, -4, -5, -6, -9, -11, -12, -15, -17, -18, -20, -21, -24, -25]) (countLit q [-27, -29, -31, -32, -34, -37, -39, -40, -43, -45, -46, -48, -51, -53]) (count851 q) 6 2 (meaning788 q) (meaning838 q) (meaning858 q) hs
  change valuationOf q 788 = false ∨ valuationOf q 838 = false ∨ valuationOf q 858 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause592 (q : Snake 81) (h : Conditions q) : valuation q 788 = false ∨ valuation q 838 = false ∨ valuation q 858 = true := counterClause592 (baseVal q)

theorem counterClause593 (q : Nat → Bool) : valuationOf q 788 = false ∨ valuationOf q 839 = false ∨ valuationOf q 859 = true := by
  have hs : count851 q = (countLit q [-1, -4, -5, -6, -9, -11, -12, -15, -17, -18, -20, -21, -24, -25]) + (countLit q [-27, -29, -31, -32, -34, -37, -39, -40, -43, -45, -46, -48, -51, -53]) := List.countP_append (p := literal q) (l₁ := [-1, -4, -5, -6, -9, -11, -12, -15, -17, -18, -20, -21, -24, -25]) (l₂ := [-27, -29, -31, -32, -34, -37, -39, -40, -43, -45, -46, -48, -51, -53])
  have hm := merge_two (literal (valuationOf q) (788)) (literal (valuationOf q) (839)) (literal (valuationOf q) (859)) (countLit q [-1, -4, -5, -6, -9, -11, -12, -15, -17, -18, -20, -21, -24, -25]) (countLit q [-27, -29, -31, -32, -34, -37, -39, -40, -43, -45, -46, -48, -51, -53]) (count851 q) 6 3 (meaning788 q) (meaning839 q) (meaning859 q) hs
  change valuationOf q 788 = false ∨ valuationOf q 839 = false ∨ valuationOf q 859 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause593 (q : Snake 81) (h : Conditions q) : valuation q 788 = false ∨ valuation q 839 = false ∨ valuation q 859 = true := counterClause593 (baseVal q)

theorem counterClause594 (q : Nat → Bool) : valuationOf q 788 = false ∨ valuationOf q 840 = false ∨ valuationOf q 860 = true := by
  have hs : count851 q = (countLit q [-1, -4, -5, -6, -9, -11, -12, -15, -17, -18, -20, -21, -24, -25]) + (countLit q [-27, -29, -31, -32, -34, -37, -39, -40, -43, -45, -46, -48, -51, -53]) := List.countP_append (p := literal q) (l₁ := [-1, -4, -5, -6, -9, -11, -12, -15, -17, -18, -20, -21, -24, -25]) (l₂ := [-27, -29, -31, -32, -34, -37, -39, -40, -43, -45, -46, -48, -51, -53])
  have hm := merge_two (literal (valuationOf q) (788)) (literal (valuationOf q) (840)) (literal (valuationOf q) (860)) (countLit q [-1, -4, -5, -6, -9, -11, -12, -15, -17, -18, -20, -21, -24, -25]) (countLit q [-27, -29, -31, -32, -34, -37, -39, -40, -43, -45, -46, -48, -51, -53]) (count851 q) 6 4 (meaning788 q) (meaning840 q) (meaning860 q) hs
  change valuationOf q 788 = false ∨ valuationOf q 840 = false ∨ valuationOf q 860 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause594 (q : Snake 81) (h : Conditions q) : valuation q 788 = false ∨ valuation q 840 = false ∨ valuation q 860 = true := counterClause594 (baseVal q)

theorem counterClause595 (q : Nat → Bool) : valuationOf q 788 = false ∨ valuationOf q 841 = false ∨ valuationOf q 861 = true := by
  have hs : count851 q = (countLit q [-1, -4, -5, -6, -9, -11, -12, -15, -17, -18, -20, -21, -24, -25]) + (countLit q [-27, -29, -31, -32, -34, -37, -39, -40, -43, -45, -46, -48, -51, -53]) := List.countP_append (p := literal q) (l₁ := [-1, -4, -5, -6, -9, -11, -12, -15, -17, -18, -20, -21, -24, -25]) (l₂ := [-27, -29, -31, -32, -34, -37, -39, -40, -43, -45, -46, -48, -51, -53])
  have hm := merge_two (literal (valuationOf q) (788)) (literal (valuationOf q) (841)) (literal (valuationOf q) (861)) (countLit q [-1, -4, -5, -6, -9, -11, -12, -15, -17, -18, -20, -21, -24, -25]) (countLit q [-27, -29, -31, -32, -34, -37, -39, -40, -43, -45, -46, -48, -51, -53]) (count851 q) 6 5 (meaning788 q) (meaning841 q) (meaning861 q) hs
  change valuationOf q 788 = false ∨ valuationOf q 841 = false ∨ valuationOf q 861 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause595 (q : Snake 81) (h : Conditions q) : valuation q 788 = false ∨ valuation q 841 = false ∨ valuation q 861 = true := counterClause595 (baseVal q)

theorem counterClause596 (q : Nat → Bool) : valuationOf q 788 = false ∨ valuationOf q 842 = false ∨ valuationOf q 862 = true := by
  have hs : count851 q = (countLit q [-1, -4, -5, -6, -9, -11, -12, -15, -17, -18, -20, -21, -24, -25]) + (countLit q [-27, -29, -31, -32, -34, -37, -39, -40, -43, -45, -46, -48, -51, -53]) := List.countP_append (p := literal q) (l₁ := [-1, -4, -5, -6, -9, -11, -12, -15, -17, -18, -20, -21, -24, -25]) (l₂ := [-27, -29, -31, -32, -34, -37, -39, -40, -43, -45, -46, -48, -51, -53])
  have hm := merge_two (literal (valuationOf q) (788)) (literal (valuationOf q) (842)) (literal (valuationOf q) (862)) (countLit q [-1, -4, -5, -6, -9, -11, -12, -15, -17, -18, -20, -21, -24, -25]) (countLit q [-27, -29, -31, -32, -34, -37, -39, -40, -43, -45, -46, -48, -51, -53]) (count851 q) 6 6 (meaning788 q) (meaning842 q) (meaning862 q) hs
  change valuationOf q 788 = false ∨ valuationOf q 842 = false ∨ valuationOf q 862 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause596 (q : Snake 81) (h : Conditions q) : valuation q 788 = false ∨ valuation q 842 = false ∨ valuation q 862 = true := counterClause596 (baseVal q)

theorem counterClause597 (q : Nat → Bool) : valuationOf q 789 = false ∨ valuationOf q 838 = false ∨ valuationOf q 859 = true := by
  have hs : count851 q = (countLit q [-1, -4, -5, -6, -9, -11, -12, -15, -17, -18, -20, -21, -24, -25]) + (countLit q [-27, -29, -31, -32, -34, -37, -39, -40, -43, -45, -46, -48, -51, -53]) := List.countP_append (p := literal q) (l₁ := [-1, -4, -5, -6, -9, -11, -12, -15, -17, -18, -20, -21, -24, -25]) (l₂ := [-27, -29, -31, -32, -34, -37, -39, -40, -43, -45, -46, -48, -51, -53])
  have hm := merge_two (literal (valuationOf q) (789)) (literal (valuationOf q) (838)) (literal (valuationOf q) (859)) (countLit q [-1, -4, -5, -6, -9, -11, -12, -15, -17, -18, -20, -21, -24, -25]) (countLit q [-27, -29, -31, -32, -34, -37, -39, -40, -43, -45, -46, -48, -51, -53]) (count851 q) 7 2 (meaning789 q) (meaning838 q) (meaning859 q) hs
  change valuationOf q 789 = false ∨ valuationOf q 838 = false ∨ valuationOf q 859 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause597 (q : Snake 81) (h : Conditions q) : valuation q 789 = false ∨ valuation q 838 = false ∨ valuation q 859 = true := counterClause597 (baseVal q)

theorem counterClause598 (q : Nat → Bool) : valuationOf q 789 = false ∨ valuationOf q 839 = false ∨ valuationOf q 860 = true := by
  have hs : count851 q = (countLit q [-1, -4, -5, -6, -9, -11, -12, -15, -17, -18, -20, -21, -24, -25]) + (countLit q [-27, -29, -31, -32, -34, -37, -39, -40, -43, -45, -46, -48, -51, -53]) := List.countP_append (p := literal q) (l₁ := [-1, -4, -5, -6, -9, -11, -12, -15, -17, -18, -20, -21, -24, -25]) (l₂ := [-27, -29, -31, -32, -34, -37, -39, -40, -43, -45, -46, -48, -51, -53])
  have hm := merge_two (literal (valuationOf q) (789)) (literal (valuationOf q) (839)) (literal (valuationOf q) (860)) (countLit q [-1, -4, -5, -6, -9, -11, -12, -15, -17, -18, -20, -21, -24, -25]) (countLit q [-27, -29, -31, -32, -34, -37, -39, -40, -43, -45, -46, -48, -51, -53]) (count851 q) 7 3 (meaning789 q) (meaning839 q) (meaning860 q) hs
  change valuationOf q 789 = false ∨ valuationOf q 839 = false ∨ valuationOf q 860 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause598 (q : Snake 81) (h : Conditions q) : valuation q 789 = false ∨ valuation q 839 = false ∨ valuation q 860 = true := counterClause598 (baseVal q)

theorem counterClause599 (q : Nat → Bool) : valuationOf q 789 = false ∨ valuationOf q 840 = false ∨ valuationOf q 861 = true := by
  have hs : count851 q = (countLit q [-1, -4, -5, -6, -9, -11, -12, -15, -17, -18, -20, -21, -24, -25]) + (countLit q [-27, -29, -31, -32, -34, -37, -39, -40, -43, -45, -46, -48, -51, -53]) := List.countP_append (p := literal q) (l₁ := [-1, -4, -5, -6, -9, -11, -12, -15, -17, -18, -20, -21, -24, -25]) (l₂ := [-27, -29, -31, -32, -34, -37, -39, -40, -43, -45, -46, -48, -51, -53])
  have hm := merge_two (literal (valuationOf q) (789)) (literal (valuationOf q) (840)) (literal (valuationOf q) (861)) (countLit q [-1, -4, -5, -6, -9, -11, -12, -15, -17, -18, -20, -21, -24, -25]) (countLit q [-27, -29, -31, -32, -34, -37, -39, -40, -43, -45, -46, -48, -51, -53]) (count851 q) 7 4 (meaning789 q) (meaning840 q) (meaning861 q) hs
  change valuationOf q 789 = false ∨ valuationOf q 840 = false ∨ valuationOf q 861 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause599 (q : Snake 81) (h : Conditions q) : valuation q 789 = false ∨ valuation q 840 = false ∨ valuation q 861 = true := counterClause599 (baseVal q)

theorem counterClause600 (q : Nat → Bool) : valuationOf q 790 = false ∨ valuationOf q 838 = false ∨ valuationOf q 860 = true := by
  have hs : count851 q = (countLit q [-1, -4, -5, -6, -9, -11, -12, -15, -17, -18, -20, -21, -24, -25]) + (countLit q [-27, -29, -31, -32, -34, -37, -39, -40, -43, -45, -46, -48, -51, -53]) := List.countP_append (p := literal q) (l₁ := [-1, -4, -5, -6, -9, -11, -12, -15, -17, -18, -20, -21, -24, -25]) (l₂ := [-27, -29, -31, -32, -34, -37, -39, -40, -43, -45, -46, -48, -51, -53])
  have hm := merge_two (literal (valuationOf q) (790)) (literal (valuationOf q) (838)) (literal (valuationOf q) (860)) (countLit q [-1, -4, -5, -6, -9, -11, -12, -15, -17, -18, -20, -21, -24, -25]) (countLit q [-27, -29, -31, -32, -34, -37, -39, -40, -43, -45, -46, -48, -51, -53]) (count851 q) 8 2 (meaning790 q) (meaning838 q) (meaning860 q) hs
  change valuationOf q 790 = false ∨ valuationOf q 838 = false ∨ valuationOf q 860 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause600 (q : Snake 81) (h : Conditions q) : valuation q 790 = false ∨ valuation q 838 = false ∨ valuation q 860 = true := counterClause600 (baseVal q)

theorem counterClause601 (q : Nat → Bool) : valuationOf q 790 = false ∨ valuationOf q 839 = false ∨ valuationOf q 861 = true := by
  have hs : count851 q = (countLit q [-1, -4, -5, -6, -9, -11, -12, -15, -17, -18, -20, -21, -24, -25]) + (countLit q [-27, -29, -31, -32, -34, -37, -39, -40, -43, -45, -46, -48, -51, -53]) := List.countP_append (p := literal q) (l₁ := [-1, -4, -5, -6, -9, -11, -12, -15, -17, -18, -20, -21, -24, -25]) (l₂ := [-27, -29, -31, -32, -34, -37, -39, -40, -43, -45, -46, -48, -51, -53])
  have hm := merge_two (literal (valuationOf q) (790)) (literal (valuationOf q) (839)) (literal (valuationOf q) (861)) (countLit q [-1, -4, -5, -6, -9, -11, -12, -15, -17, -18, -20, -21, -24, -25]) (countLit q [-27, -29, -31, -32, -34, -37, -39, -40, -43, -45, -46, -48, -51, -53]) (count851 q) 8 3 (meaning790 q) (meaning839 q) (meaning861 q) hs
  change valuationOf q 790 = false ∨ valuationOf q 839 = false ∨ valuationOf q 861 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause601 (q : Snake 81) (h : Conditions q) : valuation q 790 = false ∨ valuation q 839 = false ∨ valuation q 861 = true := counterClause601 (baseVal q)

theorem counterClause602 (q : Nat → Bool) : valuationOf q 59 = true ∨ valuationOf q 867 = true := by
  have hs : count867 q = (countLit q [-56]) + (countLit q [-59]) := List.countP_append (p := literal q) (l₁ := [-56]) (l₂ := [-59])
  have hm := merge_right (literal (valuationOf q) (-59)) (literal (valuationOf q) (867)) (countLit q [-56]) (countLit q [-59]) (count867 q) 1 (meaningNeg59 q) (meaning867 q) hs
  change (! (valuationOf q 59)) = false ∨ valuationOf q 867 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause602 (q : Snake 81) (h : Conditions q) : valuation q 59 = true ∨ valuation q 867 = true := counterClause602 (baseVal q)

theorem counterClause603 (q : Nat → Bool) : valuationOf q 56 = true ∨ valuationOf q 867 = true := by
  have hs : count867 q = (countLit q [-56]) + (countLit q [-59]) := List.countP_append (p := literal q) (l₁ := [-56]) (l₂ := [-59])
  have hm := merge_left (literal (valuationOf q) (-56)) (literal (valuationOf q) (867)) (countLit q [-56]) (countLit q [-59]) (count867 q) 1 (meaningNeg56 q) (meaning867 q) hs
  change (! (valuationOf q 56)) = false ∨ valuationOf q 867 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause603 (q : Snake 81) (h : Conditions q) : valuation q 56 = true ∨ valuation q 867 = true := counterClause603 (baseVal q)

theorem counterClause604 (q : Nat → Bool) : valuationOf q 56 = true ∨ valuationOf q 59 = true ∨ valuationOf q 868 = true := by
  have hs : count867 q = (countLit q [-56]) + (countLit q [-59]) := List.countP_append (p := literal q) (l₁ := [-56]) (l₂ := [-59])
  have hm := merge_two (literal (valuationOf q) (-56)) (literal (valuationOf q) (-59)) (literal (valuationOf q) (868)) (countLit q [-56]) (countLit q [-59]) (count867 q) 1 1 (meaningNeg56 q) (meaningNeg59 q) (meaning868 q) hs
  change (! (valuationOf q 56)) = false ∨ (! (valuationOf q 59)) = false ∨ valuationOf q 868 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause604 (q : Snake 81) (h : Conditions q) : valuation q 56 = true ∨ valuation q 59 = true ∨ valuation q 868 = true := counterClause604 (baseVal q)

theorem counterClause605 (q : Nat → Bool) : valuationOf q 867 = false ∨ valuationOf q 869 = true := by
  have hs : count869 q = (countLit q [-54]) + (countLit q [-56, -59]) := List.countP_append (p := literal q) (l₁ := [-54]) (l₂ := [-56, -59])
  have hm := merge_right (literal (valuationOf q) (867)) (literal (valuationOf q) (869)) (countLit q [-54]) (countLit q [-56, -59]) (count869 q) 1 (meaning867 q) (meaning869 q) hs
  change valuationOf q 867 = false ∨ valuationOf q 869 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause605 (q : Snake 81) (h : Conditions q) : valuation q 867 = false ∨ valuation q 869 = true := counterClause605 (baseVal q)

theorem counterClause606 (q : Nat → Bool) : valuationOf q 868 = false ∨ valuationOf q 870 = true := by
  have hs : count869 q = (countLit q [-54]) + (countLit q [-56, -59]) := List.countP_append (p := literal q) (l₁ := [-54]) (l₂ := [-56, -59])
  have hm := merge_right (literal (valuationOf q) (868)) (literal (valuationOf q) (870)) (countLit q [-54]) (countLit q [-56, -59]) (count869 q) 2 (meaning868 q) (meaning870 q) hs
  change valuationOf q 868 = false ∨ valuationOf q 870 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause606 (q : Snake 81) (h : Conditions q) : valuation q 868 = false ∨ valuation q 870 = true := counterClause606 (baseVal q)

theorem counterClause607 (q : Nat → Bool) : valuationOf q 54 = true ∨ valuationOf q 869 = true := by
  have hs : count869 q = (countLit q [-54]) + (countLit q [-56, -59]) := List.countP_append (p := literal q) (l₁ := [-54]) (l₂ := [-56, -59])
  have hm := merge_left (literal (valuationOf q) (-54)) (literal (valuationOf q) (869)) (countLit q [-54]) (countLit q [-56, -59]) (count869 q) 1 (meaningNeg54 q) (meaning869 q) hs
  change (! (valuationOf q 54)) = false ∨ valuationOf q 869 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause607 (q : Snake 81) (h : Conditions q) : valuation q 54 = true ∨ valuation q 869 = true := counterClause607 (baseVal q)

theorem counterClause608 (q : Nat → Bool) : valuationOf q 54 = true ∨ valuationOf q 867 = false ∨ valuationOf q 870 = true := by
  have hs : count869 q = (countLit q [-54]) + (countLit q [-56, -59]) := List.countP_append (p := literal q) (l₁ := [-54]) (l₂ := [-56, -59])
  have hm := merge_two (literal (valuationOf q) (-54)) (literal (valuationOf q) (867)) (literal (valuationOf q) (870)) (countLit q [-54]) (countLit q [-56, -59]) (count869 q) 1 1 (meaningNeg54 q) (meaning867 q) (meaning870 q) hs
  change (! (valuationOf q 54)) = false ∨ valuationOf q 867 = false ∨ valuationOf q 870 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause608 (q : Snake 81) (h : Conditions q) : valuation q 54 = true ∨ valuation q 867 = false ∨ valuation q 870 = true := counterClause608 (baseVal q)

theorem block18 (q : Snake 81) (h : Conditions q) : B112E185.Block18 (valuation q) :=
  ⟨clause577 q h, clause578 q h, clause579 q h, clause580 q h, clause581 q h, clause582 q h, clause583 q h, clause584 q h, clause585 q h, clause586 q h, clause587 q h, clause588 q h, clause589 q h, clause590 q h, clause591 q h, clause592 q h, clause593 q h, clause594 q h, clause595 q h, clause596 q h, clause597 q h, clause598 q h, clause599 q h, clause600 q h, clause601 q h, clause602 q h, clause603 q h, clause604 q h, clause605 q h, clause606 q h, clause607 q h, clause608 q h⟩

end
end Snake9.Regrowth.E112185
