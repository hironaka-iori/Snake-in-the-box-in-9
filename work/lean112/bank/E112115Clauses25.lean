import E112115Semantics
import B112E115Inputs
namespace Snake9.Regrowth.E112115
noncomputable section
local instance blockDec25 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause801 (q : Nat → Bool) : valuationOf q 820 = false ∨ valuationOf q 826 = false ∨ valuationOf q 832 = true := by
  have hs : count830 q = (countLit q [-16, -18, -19]) + (countLit q [-21, -22, -24, -25]) := List.countP_append (p := literal q) (l₁ := [-16, -18, -19]) (l₂ := [-21, -22, -24, -25])
  have hm := merge_two (literal (valuationOf q) (820)) (literal (valuationOf q) (826)) (literal (valuationOf q) (832)) (countLit q [-16, -18, -19]) (countLit q [-21, -22, -24, -25]) (count830 q) 2 1 (meaning820 q) (meaning826 q) (meaning832 q) hs
  change valuationOf q 820 = false ∨ valuationOf q 826 = false ∨ valuationOf q 832 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause801 (q : Snake 81) (h : Conditions q) : valuation q 820 = false ∨ valuation q 826 = false ∨ valuation q 832 = true := counterClause801 (baseVal q)

theorem counterClause802 (q : Nat → Bool) : valuationOf q 820 = false ∨ valuationOf q 827 = false ∨ valuationOf q 833 = true := by
  have hs : count830 q = (countLit q [-16, -18, -19]) + (countLit q [-21, -22, -24, -25]) := List.countP_append (p := literal q) (l₁ := [-16, -18, -19]) (l₂ := [-21, -22, -24, -25])
  have hm := merge_two (literal (valuationOf q) (820)) (literal (valuationOf q) (827)) (literal (valuationOf q) (833)) (countLit q [-16, -18, -19]) (countLit q [-21, -22, -24, -25]) (count830 q) 2 2 (meaning820 q) (meaning827 q) (meaning833 q) hs
  change valuationOf q 820 = false ∨ valuationOf q 827 = false ∨ valuationOf q 833 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause802 (q : Snake 81) (h : Conditions q) : valuation q 820 = false ∨ valuation q 827 = false ∨ valuation q 833 = true := counterClause802 (baseVal q)

theorem counterClause803 (q : Nat → Bool) : valuationOf q 820 = false ∨ valuationOf q 828 = false ∨ valuationOf q 834 = true := by
  have hs : count830 q = (countLit q [-16, -18, -19]) + (countLit q [-21, -22, -24, -25]) := List.countP_append (p := literal q) (l₁ := [-16, -18, -19]) (l₂ := [-21, -22, -24, -25])
  have hm := merge_two (literal (valuationOf q) (820)) (literal (valuationOf q) (828)) (literal (valuationOf q) (834)) (countLit q [-16, -18, -19]) (countLit q [-21, -22, -24, -25]) (count830 q) 2 3 (meaning820 q) (meaning828 q) (meaning834 q) hs
  change valuationOf q 820 = false ∨ valuationOf q 828 = false ∨ valuationOf q 834 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause803 (q : Snake 81) (h : Conditions q) : valuation q 820 = false ∨ valuation q 828 = false ∨ valuation q 834 = true := counterClause803 (baseVal q)

theorem counterClause804 (q : Nat → Bool) : valuationOf q 821 = false ∨ valuationOf q 832 = true := by
  have hs : count830 q = (countLit q [-16, -18, -19]) + (countLit q [-21, -22, -24, -25]) := List.countP_append (p := literal q) (l₁ := [-16, -18, -19]) (l₂ := [-21, -22, -24, -25])
  have hm := merge_left (literal (valuationOf q) (821)) (literal (valuationOf q) (832)) (countLit q [-16, -18, -19]) (countLit q [-21, -22, -24, -25]) (count830 q) 3 (meaning821 q) (meaning832 q) hs
  change valuationOf q 821 = false ∨ valuationOf q 832 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause804 (q : Snake 81) (h : Conditions q) : valuation q 821 = false ∨ valuation q 832 = true := counterClause804 (baseVal q)

theorem counterClause805 (q : Nat → Bool) : valuationOf q 821 = false ∨ valuationOf q 826 = false ∨ valuationOf q 833 = true := by
  have hs : count830 q = (countLit q [-16, -18, -19]) + (countLit q [-21, -22, -24, -25]) := List.countP_append (p := literal q) (l₁ := [-16, -18, -19]) (l₂ := [-21, -22, -24, -25])
  have hm := merge_two (literal (valuationOf q) (821)) (literal (valuationOf q) (826)) (literal (valuationOf q) (833)) (countLit q [-16, -18, -19]) (countLit q [-21, -22, -24, -25]) (count830 q) 3 1 (meaning821 q) (meaning826 q) (meaning833 q) hs
  change valuationOf q 821 = false ∨ valuationOf q 826 = false ∨ valuationOf q 833 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause805 (q : Snake 81) (h : Conditions q) : valuation q 821 = false ∨ valuation q 826 = false ∨ valuation q 833 = true := counterClause805 (baseVal q)

theorem counterClause806 (q : Nat → Bool) : valuationOf q 821 = false ∨ valuationOf q 827 = false ∨ valuationOf q 834 = true := by
  have hs : count830 q = (countLit q [-16, -18, -19]) + (countLit q [-21, -22, -24, -25]) := List.countP_append (p := literal q) (l₁ := [-16, -18, -19]) (l₂ := [-21, -22, -24, -25])
  have hm := merge_two (literal (valuationOf q) (821)) (literal (valuationOf q) (827)) (literal (valuationOf q) (834)) (countLit q [-16, -18, -19]) (countLit q [-21, -22, -24, -25]) (count830 q) 3 2 (meaning821 q) (meaning827 q) (meaning834 q) hs
  change valuationOf q 821 = false ∨ valuationOf q 827 = false ∨ valuationOf q 834 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause806 (q : Snake 81) (h : Conditions q) : valuation q 821 = false ∨ valuation q 827 = false ∨ valuation q 834 = true := counterClause806 (baseVal q)

theorem counterClause807 (q : Nat → Bool) : valuationOf q 821 = false ∨ valuationOf q 828 = false ∨ valuationOf q 835 = true := by
  have hs : count830 q = (countLit q [-16, -18, -19]) + (countLit q [-21, -22, -24, -25]) := List.countP_append (p := literal q) (l₁ := [-16, -18, -19]) (l₂ := [-21, -22, -24, -25])
  have hm := merge_two (literal (valuationOf q) (821)) (literal (valuationOf q) (828)) (literal (valuationOf q) (835)) (countLit q [-16, -18, -19]) (countLit q [-21, -22, -24, -25]) (count830 q) 3 3 (meaning821 q) (meaning828 q) (meaning835 q) hs
  change valuationOf q 821 = false ∨ valuationOf q 828 = false ∨ valuationOf q 835 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause807 (q : Snake 81) (h : Conditions q) : valuation q 821 = false ∨ valuation q 828 = false ∨ valuation q 835 = true := counterClause807 (baseVal q)

theorem counterClause808 (q : Nat → Bool) : valuationOf q 830 = false ∨ valuationOf q 837 = true := by
  have hs : count837 q = (countLit q [-1, -4, -7, -9, -11, -13, -14]) + (countLit q [-16, -18, -19, -21, -22, -24, -25]) := List.countP_append (p := literal q) (l₁ := [-1, -4, -7, -9, -11, -13, -14]) (l₂ := [-16, -18, -19, -21, -22, -24, -25])
  have hm := merge_right (literal (valuationOf q) (830)) (literal (valuationOf q) (837)) (countLit q [-1, -4, -7, -9, -11, -13, -14]) (countLit q [-16, -18, -19, -21, -22, -24, -25]) (count837 q) 1 (meaning830 q) (meaning837 q) hs
  change valuationOf q 830 = false ∨ valuationOf q 837 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause808 (q : Snake 81) (h : Conditions q) : valuation q 830 = false ∨ valuation q 837 = true := counterClause808 (baseVal q)

theorem counterClause809 (q : Nat → Bool) : valuationOf q 831 = false ∨ valuationOf q 838 = true := by
  have hs : count837 q = (countLit q [-1, -4, -7, -9, -11, -13, -14]) + (countLit q [-16, -18, -19, -21, -22, -24, -25]) := List.countP_append (p := literal q) (l₁ := [-1, -4, -7, -9, -11, -13, -14]) (l₂ := [-16, -18, -19, -21, -22, -24, -25])
  have hm := merge_right (literal (valuationOf q) (831)) (literal (valuationOf q) (838)) (countLit q [-1, -4, -7, -9, -11, -13, -14]) (countLit q [-16, -18, -19, -21, -22, -24, -25]) (count837 q) 2 (meaning831 q) (meaning838 q) hs
  change valuationOf q 831 = false ∨ valuationOf q 838 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause809 (q : Snake 81) (h : Conditions q) : valuation q 831 = false ∨ valuation q 838 = true := counterClause809 (baseVal q)

theorem counterClause810 (q : Nat → Bool) : valuationOf q 832 = false ∨ valuationOf q 839 = true := by
  have hs : count837 q = (countLit q [-1, -4, -7, -9, -11, -13, -14]) + (countLit q [-16, -18, -19, -21, -22, -24, -25]) := List.countP_append (p := literal q) (l₁ := [-1, -4, -7, -9, -11, -13, -14]) (l₂ := [-16, -18, -19, -21, -22, -24, -25])
  have hm := merge_right (literal (valuationOf q) (832)) (literal (valuationOf q) (839)) (countLit q [-1, -4, -7, -9, -11, -13, -14]) (countLit q [-16, -18, -19, -21, -22, -24, -25]) (count837 q) 3 (meaning832 q) (meaning839 q) hs
  change valuationOf q 832 = false ∨ valuationOf q 839 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause810 (q : Snake 81) (h : Conditions q) : valuation q 832 = false ∨ valuation q 839 = true := counterClause810 (baseVal q)

theorem counterClause811 (q : Nat → Bool) : valuationOf q 833 = false ∨ valuationOf q 840 = true := by
  have hs : count837 q = (countLit q [-1, -4, -7, -9, -11, -13, -14]) + (countLit q [-16, -18, -19, -21, -22, -24, -25]) := List.countP_append (p := literal q) (l₁ := [-1, -4, -7, -9, -11, -13, -14]) (l₂ := [-16, -18, -19, -21, -22, -24, -25])
  have hm := merge_right (literal (valuationOf q) (833)) (literal (valuationOf q) (840)) (countLit q [-1, -4, -7, -9, -11, -13, -14]) (countLit q [-16, -18, -19, -21, -22, -24, -25]) (count837 q) 4 (meaning833 q) (meaning840 q) hs
  change valuationOf q 833 = false ∨ valuationOf q 840 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause811 (q : Snake 81) (h : Conditions q) : valuation q 833 = false ∨ valuation q 840 = true := counterClause811 (baseVal q)

theorem counterClause812 (q : Nat → Bool) : valuationOf q 810 = false ∨ valuationOf q 830 = false ∨ valuationOf q 838 = true := by
  have hs : count837 q = (countLit q [-1, -4, -7, -9, -11, -13, -14]) + (countLit q [-16, -18, -19, -21, -22, -24, -25]) := List.countP_append (p := literal q) (l₁ := [-1, -4, -7, -9, -11, -13, -14]) (l₂ := [-16, -18, -19, -21, -22, -24, -25])
  have hm := merge_two (literal (valuationOf q) (810)) (literal (valuationOf q) (830)) (literal (valuationOf q) (838)) (countLit q [-1, -4, -7, -9, -11, -13, -14]) (countLit q [-16, -18, -19, -21, -22, -24, -25]) (count837 q) 1 1 (meaning810 q) (meaning830 q) (meaning838 q) hs
  change valuationOf q 810 = false ∨ valuationOf q 830 = false ∨ valuationOf q 838 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause812 (q : Snake 81) (h : Conditions q) : valuation q 810 = false ∨ valuation q 830 = false ∨ valuation q 838 = true := counterClause812 (baseVal q)

theorem counterClause813 (q : Nat → Bool) : valuationOf q 810 = false ∨ valuationOf q 831 = false ∨ valuationOf q 839 = true := by
  have hs : count837 q = (countLit q [-1, -4, -7, -9, -11, -13, -14]) + (countLit q [-16, -18, -19, -21, -22, -24, -25]) := List.countP_append (p := literal q) (l₁ := [-1, -4, -7, -9, -11, -13, -14]) (l₂ := [-16, -18, -19, -21, -22, -24, -25])
  have hm := merge_two (literal (valuationOf q) (810)) (literal (valuationOf q) (831)) (literal (valuationOf q) (839)) (countLit q [-1, -4, -7, -9, -11, -13, -14]) (countLit q [-16, -18, -19, -21, -22, -24, -25]) (count837 q) 1 2 (meaning810 q) (meaning831 q) (meaning839 q) hs
  change valuationOf q 810 = false ∨ valuationOf q 831 = false ∨ valuationOf q 839 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause813 (q : Snake 81) (h : Conditions q) : valuation q 810 = false ∨ valuation q 831 = false ∨ valuation q 839 = true := counterClause813 (baseVal q)

theorem counterClause814 (q : Nat → Bool) : valuationOf q 810 = false ∨ valuationOf q 832 = false ∨ valuationOf q 840 = true := by
  have hs : count837 q = (countLit q [-1, -4, -7, -9, -11, -13, -14]) + (countLit q [-16, -18, -19, -21, -22, -24, -25]) := List.countP_append (p := literal q) (l₁ := [-1, -4, -7, -9, -11, -13, -14]) (l₂ := [-16, -18, -19, -21, -22, -24, -25])
  have hm := merge_two (literal (valuationOf q) (810)) (literal (valuationOf q) (832)) (literal (valuationOf q) (840)) (countLit q [-1, -4, -7, -9, -11, -13, -14]) (countLit q [-16, -18, -19, -21, -22, -24, -25]) (count837 q) 1 3 (meaning810 q) (meaning832 q) (meaning840 q) hs
  change valuationOf q 810 = false ∨ valuationOf q 832 = false ∨ valuationOf q 840 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause814 (q : Snake 81) (h : Conditions q) : valuation q 810 = false ∨ valuation q 832 = false ∨ valuation q 840 = true := counterClause814 (baseVal q)

theorem counterClause815 (q : Nat → Bool) : valuationOf q 810 = false ∨ valuationOf q 833 = false ∨ valuationOf q 841 = true := by
  have hs : count837 q = (countLit q [-1, -4, -7, -9, -11, -13, -14]) + (countLit q [-16, -18, -19, -21, -22, -24, -25]) := List.countP_append (p := literal q) (l₁ := [-1, -4, -7, -9, -11, -13, -14]) (l₂ := [-16, -18, -19, -21, -22, -24, -25])
  have hm := merge_two (literal (valuationOf q) (810)) (literal (valuationOf q) (833)) (literal (valuationOf q) (841)) (countLit q [-1, -4, -7, -9, -11, -13, -14]) (countLit q [-16, -18, -19, -21, -22, -24, -25]) (count837 q) 1 4 (meaning810 q) (meaning833 q) (meaning841 q) hs
  change valuationOf q 810 = false ∨ valuationOf q 833 = false ∨ valuationOf q 841 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause815 (q : Snake 81) (h : Conditions q) : valuation q 810 = false ∨ valuation q 833 = false ∨ valuation q 841 = true := counterClause815 (baseVal q)

theorem counterClause816 (q : Nat → Bool) : valuationOf q 810 = false ∨ valuationOf q 834 = false ∨ valuationOf q 842 = true := by
  have hs : count837 q = (countLit q [-1, -4, -7, -9, -11, -13, -14]) + (countLit q [-16, -18, -19, -21, -22, -24, -25]) := List.countP_append (p := literal q) (l₁ := [-1, -4, -7, -9, -11, -13, -14]) (l₂ := [-16, -18, -19, -21, -22, -24, -25])
  have hm := merge_two (literal (valuationOf q) (810)) (literal (valuationOf q) (834)) (literal (valuationOf q) (842)) (countLit q [-1, -4, -7, -9, -11, -13, -14]) (countLit q [-16, -18, -19, -21, -22, -24, -25]) (count837 q) 1 5 (meaning810 q) (meaning834 q) (meaning842 q) hs
  change valuationOf q 810 = false ∨ valuationOf q 834 = false ∨ valuationOf q 842 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause816 (q : Snake 81) (h : Conditions q) : valuation q 810 = false ∨ valuation q 834 = false ∨ valuation q 842 = true := counterClause816 (baseVal q)

theorem counterClause817 (q : Nat → Bool) : valuationOf q 811 = false ∨ valuationOf q 830 = false ∨ valuationOf q 839 = true := by
  have hs : count837 q = (countLit q [-1, -4, -7, -9, -11, -13, -14]) + (countLit q [-16, -18, -19, -21, -22, -24, -25]) := List.countP_append (p := literal q) (l₁ := [-1, -4, -7, -9, -11, -13, -14]) (l₂ := [-16, -18, -19, -21, -22, -24, -25])
  have hm := merge_two (literal (valuationOf q) (811)) (literal (valuationOf q) (830)) (literal (valuationOf q) (839)) (countLit q [-1, -4, -7, -9, -11, -13, -14]) (countLit q [-16, -18, -19, -21, -22, -24, -25]) (count837 q) 2 1 (meaning811 q) (meaning830 q) (meaning839 q) hs
  change valuationOf q 811 = false ∨ valuationOf q 830 = false ∨ valuationOf q 839 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause817 (q : Snake 81) (h : Conditions q) : valuation q 811 = false ∨ valuation q 830 = false ∨ valuation q 839 = true := counterClause817 (baseVal q)

theorem counterClause818 (q : Nat → Bool) : valuationOf q 811 = false ∨ valuationOf q 831 = false ∨ valuationOf q 840 = true := by
  have hs : count837 q = (countLit q [-1, -4, -7, -9, -11, -13, -14]) + (countLit q [-16, -18, -19, -21, -22, -24, -25]) := List.countP_append (p := literal q) (l₁ := [-1, -4, -7, -9, -11, -13, -14]) (l₂ := [-16, -18, -19, -21, -22, -24, -25])
  have hm := merge_two (literal (valuationOf q) (811)) (literal (valuationOf q) (831)) (literal (valuationOf q) (840)) (countLit q [-1, -4, -7, -9, -11, -13, -14]) (countLit q [-16, -18, -19, -21, -22, -24, -25]) (count837 q) 2 2 (meaning811 q) (meaning831 q) (meaning840 q) hs
  change valuationOf q 811 = false ∨ valuationOf q 831 = false ∨ valuationOf q 840 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause818 (q : Snake 81) (h : Conditions q) : valuation q 811 = false ∨ valuation q 831 = false ∨ valuation q 840 = true := counterClause818 (baseVal q)

theorem counterClause819 (q : Nat → Bool) : valuationOf q 811 = false ∨ valuationOf q 832 = false ∨ valuationOf q 841 = true := by
  have hs : count837 q = (countLit q [-1, -4, -7, -9, -11, -13, -14]) + (countLit q [-16, -18, -19, -21, -22, -24, -25]) := List.countP_append (p := literal q) (l₁ := [-1, -4, -7, -9, -11, -13, -14]) (l₂ := [-16, -18, -19, -21, -22, -24, -25])
  have hm := merge_two (literal (valuationOf q) (811)) (literal (valuationOf q) (832)) (literal (valuationOf q) (841)) (countLit q [-1, -4, -7, -9, -11, -13, -14]) (countLit q [-16, -18, -19, -21, -22, -24, -25]) (count837 q) 2 3 (meaning811 q) (meaning832 q) (meaning841 q) hs
  change valuationOf q 811 = false ∨ valuationOf q 832 = false ∨ valuationOf q 841 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause819 (q : Snake 81) (h : Conditions q) : valuation q 811 = false ∨ valuation q 832 = false ∨ valuation q 841 = true := counterClause819 (baseVal q)

theorem counterClause820 (q : Nat → Bool) : valuationOf q 811 = false ∨ valuationOf q 833 = false ∨ valuationOf q 842 = true := by
  have hs : count837 q = (countLit q [-1, -4, -7, -9, -11, -13, -14]) + (countLit q [-16, -18, -19, -21, -22, -24, -25]) := List.countP_append (p := literal q) (l₁ := [-1, -4, -7, -9, -11, -13, -14]) (l₂ := [-16, -18, -19, -21, -22, -24, -25])
  have hm := merge_two (literal (valuationOf q) (811)) (literal (valuationOf q) (833)) (literal (valuationOf q) (842)) (countLit q [-1, -4, -7, -9, -11, -13, -14]) (countLit q [-16, -18, -19, -21, -22, -24, -25]) (count837 q) 2 4 (meaning811 q) (meaning833 q) (meaning842 q) hs
  change valuationOf q 811 = false ∨ valuationOf q 833 = false ∨ valuationOf q 842 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause820 (q : Snake 81) (h : Conditions q) : valuation q 811 = false ∨ valuation q 833 = false ∨ valuation q 842 = true := counterClause820 (baseVal q)

theorem counterClause821 (q : Nat → Bool) : valuationOf q 811 = false ∨ valuationOf q 834 = false ∨ valuationOf q 843 = true := by
  have hs : count837 q = (countLit q [-1, -4, -7, -9, -11, -13, -14]) + (countLit q [-16, -18, -19, -21, -22, -24, -25]) := List.countP_append (p := literal q) (l₁ := [-1, -4, -7, -9, -11, -13, -14]) (l₂ := [-16, -18, -19, -21, -22, -24, -25])
  have hm := merge_two (literal (valuationOf q) (811)) (literal (valuationOf q) (834)) (literal (valuationOf q) (843)) (countLit q [-1, -4, -7, -9, -11, -13, -14]) (countLit q [-16, -18, -19, -21, -22, -24, -25]) (count837 q) 2 5 (meaning811 q) (meaning834 q) (meaning843 q) hs
  change valuationOf q 811 = false ∨ valuationOf q 834 = false ∨ valuationOf q 843 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause821 (q : Snake 81) (h : Conditions q) : valuation q 811 = false ∨ valuation q 834 = false ∨ valuation q 843 = true := counterClause821 (baseVal q)

theorem counterClause822 (q : Nat → Bool) : valuationOf q 811 = false ∨ valuationOf q 835 = false ∨ valuationOf q 844 = true := by
  have hs : count837 q = (countLit q [-1, -4, -7, -9, -11, -13, -14]) + (countLit q [-16, -18, -19, -21, -22, -24, -25]) := List.countP_append (p := literal q) (l₁ := [-1, -4, -7, -9, -11, -13, -14]) (l₂ := [-16, -18, -19, -21, -22, -24, -25])
  have hm := merge_two (literal (valuationOf q) (811)) (literal (valuationOf q) (835)) (literal (valuationOf q) (844)) (countLit q [-1, -4, -7, -9, -11, -13, -14]) (countLit q [-16, -18, -19, -21, -22, -24, -25]) (count837 q) 2 6 (meaning811 q) (meaning835 q) (meaning844 q) hs
  change valuationOf q 811 = false ∨ valuationOf q 835 = false ∨ valuationOf q 844 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause822 (q : Snake 81) (h : Conditions q) : valuation q 811 = false ∨ valuation q 835 = false ∨ valuation q 844 = true := counterClause822 (baseVal q)

theorem counterClause823 (q : Nat → Bool) : valuationOf q 812 = false ∨ valuationOf q 830 = false ∨ valuationOf q 840 = true := by
  have hs : count837 q = (countLit q [-1, -4, -7, -9, -11, -13, -14]) + (countLit q [-16, -18, -19, -21, -22, -24, -25]) := List.countP_append (p := literal q) (l₁ := [-1, -4, -7, -9, -11, -13, -14]) (l₂ := [-16, -18, -19, -21, -22, -24, -25])
  have hm := merge_two (literal (valuationOf q) (812)) (literal (valuationOf q) (830)) (literal (valuationOf q) (840)) (countLit q [-1, -4, -7, -9, -11, -13, -14]) (countLit q [-16, -18, -19, -21, -22, -24, -25]) (count837 q) 3 1 (meaning812 q) (meaning830 q) (meaning840 q) hs
  change valuationOf q 812 = false ∨ valuationOf q 830 = false ∨ valuationOf q 840 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause823 (q : Snake 81) (h : Conditions q) : valuation q 812 = false ∨ valuation q 830 = false ∨ valuation q 840 = true := counterClause823 (baseVal q)

theorem counterClause824 (q : Nat → Bool) : valuationOf q 812 = false ∨ valuationOf q 831 = false ∨ valuationOf q 841 = true := by
  have hs : count837 q = (countLit q [-1, -4, -7, -9, -11, -13, -14]) + (countLit q [-16, -18, -19, -21, -22, -24, -25]) := List.countP_append (p := literal q) (l₁ := [-1, -4, -7, -9, -11, -13, -14]) (l₂ := [-16, -18, -19, -21, -22, -24, -25])
  have hm := merge_two (literal (valuationOf q) (812)) (literal (valuationOf q) (831)) (literal (valuationOf q) (841)) (countLit q [-1, -4, -7, -9, -11, -13, -14]) (countLit q [-16, -18, -19, -21, -22, -24, -25]) (count837 q) 3 2 (meaning812 q) (meaning831 q) (meaning841 q) hs
  change valuationOf q 812 = false ∨ valuationOf q 831 = false ∨ valuationOf q 841 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause824 (q : Snake 81) (h : Conditions q) : valuation q 812 = false ∨ valuation q 831 = false ∨ valuation q 841 = true := counterClause824 (baseVal q)

theorem counterClause825 (q : Nat → Bool) : valuationOf q 812 = false ∨ valuationOf q 832 = false ∨ valuationOf q 842 = true := by
  have hs : count837 q = (countLit q [-1, -4, -7, -9, -11, -13, -14]) + (countLit q [-16, -18, -19, -21, -22, -24, -25]) := List.countP_append (p := literal q) (l₁ := [-1, -4, -7, -9, -11, -13, -14]) (l₂ := [-16, -18, -19, -21, -22, -24, -25])
  have hm := merge_two (literal (valuationOf q) (812)) (literal (valuationOf q) (832)) (literal (valuationOf q) (842)) (countLit q [-1, -4, -7, -9, -11, -13, -14]) (countLit q [-16, -18, -19, -21, -22, -24, -25]) (count837 q) 3 3 (meaning812 q) (meaning832 q) (meaning842 q) hs
  change valuationOf q 812 = false ∨ valuationOf q 832 = false ∨ valuationOf q 842 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause825 (q : Snake 81) (h : Conditions q) : valuation q 812 = false ∨ valuation q 832 = false ∨ valuation q 842 = true := counterClause825 (baseVal q)

theorem counterClause826 (q : Nat → Bool) : valuationOf q 812 = false ∨ valuationOf q 833 = false ∨ valuationOf q 843 = true := by
  have hs : count837 q = (countLit q [-1, -4, -7, -9, -11, -13, -14]) + (countLit q [-16, -18, -19, -21, -22, -24, -25]) := List.countP_append (p := literal q) (l₁ := [-1, -4, -7, -9, -11, -13, -14]) (l₂ := [-16, -18, -19, -21, -22, -24, -25])
  have hm := merge_two (literal (valuationOf q) (812)) (literal (valuationOf q) (833)) (literal (valuationOf q) (843)) (countLit q [-1, -4, -7, -9, -11, -13, -14]) (countLit q [-16, -18, -19, -21, -22, -24, -25]) (count837 q) 3 4 (meaning812 q) (meaning833 q) (meaning843 q) hs
  change valuationOf q 812 = false ∨ valuationOf q 833 = false ∨ valuationOf q 843 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause826 (q : Snake 81) (h : Conditions q) : valuation q 812 = false ∨ valuation q 833 = false ∨ valuation q 843 = true := counterClause826 (baseVal q)

theorem counterClause827 (q : Nat → Bool) : valuationOf q 812 = false ∨ valuationOf q 834 = false ∨ valuationOf q 844 = true := by
  have hs : count837 q = (countLit q [-1, -4, -7, -9, -11, -13, -14]) + (countLit q [-16, -18, -19, -21, -22, -24, -25]) := List.countP_append (p := literal q) (l₁ := [-1, -4, -7, -9, -11, -13, -14]) (l₂ := [-16, -18, -19, -21, -22, -24, -25])
  have hm := merge_two (literal (valuationOf q) (812)) (literal (valuationOf q) (834)) (literal (valuationOf q) (844)) (countLit q [-1, -4, -7, -9, -11, -13, -14]) (countLit q [-16, -18, -19, -21, -22, -24, -25]) (count837 q) 3 5 (meaning812 q) (meaning834 q) (meaning844 q) hs
  change valuationOf q 812 = false ∨ valuationOf q 834 = false ∨ valuationOf q 844 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause827 (q : Snake 81) (h : Conditions q) : valuation q 812 = false ∨ valuation q 834 = false ∨ valuation q 844 = true := counterClause827 (baseVal q)

theorem counterClause828 (q : Nat → Bool) : valuationOf q 812 = false ∨ valuationOf q 835 = false ∨ valuationOf q 845 = true := by
  have hs : count837 q = (countLit q [-1, -4, -7, -9, -11, -13, -14]) + (countLit q [-16, -18, -19, -21, -22, -24, -25]) := List.countP_append (p := literal q) (l₁ := [-1, -4, -7, -9, -11, -13, -14]) (l₂ := [-16, -18, -19, -21, -22, -24, -25])
  have hm := merge_two (literal (valuationOf q) (812)) (literal (valuationOf q) (835)) (literal (valuationOf q) (845)) (countLit q [-1, -4, -7, -9, -11, -13, -14]) (countLit q [-16, -18, -19, -21, -22, -24, -25]) (count837 q) 3 6 (meaning812 q) (meaning835 q) (meaning845 q) hs
  change valuationOf q 812 = false ∨ valuationOf q 835 = false ∨ valuationOf q 845 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause828 (q : Snake 81) (h : Conditions q) : valuation q 812 = false ∨ valuation q 835 = false ∨ valuation q 845 = true := counterClause828 (baseVal q)

theorem counterClause829 (q : Nat → Bool) : valuationOf q 813 = false ∨ valuationOf q 830 = false ∨ valuationOf q 841 = true := by
  have hs : count837 q = (countLit q [-1, -4, -7, -9, -11, -13, -14]) + (countLit q [-16, -18, -19, -21, -22, -24, -25]) := List.countP_append (p := literal q) (l₁ := [-1, -4, -7, -9, -11, -13, -14]) (l₂ := [-16, -18, -19, -21, -22, -24, -25])
  have hm := merge_two (literal (valuationOf q) (813)) (literal (valuationOf q) (830)) (literal (valuationOf q) (841)) (countLit q [-1, -4, -7, -9, -11, -13, -14]) (countLit q [-16, -18, -19, -21, -22, -24, -25]) (count837 q) 4 1 (meaning813 q) (meaning830 q) (meaning841 q) hs
  change valuationOf q 813 = false ∨ valuationOf q 830 = false ∨ valuationOf q 841 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause829 (q : Snake 81) (h : Conditions q) : valuation q 813 = false ∨ valuation q 830 = false ∨ valuation q 841 = true := counterClause829 (baseVal q)

theorem counterClause830 (q : Nat → Bool) : valuationOf q 813 = false ∨ valuationOf q 831 = false ∨ valuationOf q 842 = true := by
  have hs : count837 q = (countLit q [-1, -4, -7, -9, -11, -13, -14]) + (countLit q [-16, -18, -19, -21, -22, -24, -25]) := List.countP_append (p := literal q) (l₁ := [-1, -4, -7, -9, -11, -13, -14]) (l₂ := [-16, -18, -19, -21, -22, -24, -25])
  have hm := merge_two (literal (valuationOf q) (813)) (literal (valuationOf q) (831)) (literal (valuationOf q) (842)) (countLit q [-1, -4, -7, -9, -11, -13, -14]) (countLit q [-16, -18, -19, -21, -22, -24, -25]) (count837 q) 4 2 (meaning813 q) (meaning831 q) (meaning842 q) hs
  change valuationOf q 813 = false ∨ valuationOf q 831 = false ∨ valuationOf q 842 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause830 (q : Snake 81) (h : Conditions q) : valuation q 813 = false ∨ valuation q 831 = false ∨ valuation q 842 = true := counterClause830 (baseVal q)

theorem counterClause831 (q : Nat → Bool) : valuationOf q 813 = false ∨ valuationOf q 832 = false ∨ valuationOf q 843 = true := by
  have hs : count837 q = (countLit q [-1, -4, -7, -9, -11, -13, -14]) + (countLit q [-16, -18, -19, -21, -22, -24, -25]) := List.countP_append (p := literal q) (l₁ := [-1, -4, -7, -9, -11, -13, -14]) (l₂ := [-16, -18, -19, -21, -22, -24, -25])
  have hm := merge_two (literal (valuationOf q) (813)) (literal (valuationOf q) (832)) (literal (valuationOf q) (843)) (countLit q [-1, -4, -7, -9, -11, -13, -14]) (countLit q [-16, -18, -19, -21, -22, -24, -25]) (count837 q) 4 3 (meaning813 q) (meaning832 q) (meaning843 q) hs
  change valuationOf q 813 = false ∨ valuationOf q 832 = false ∨ valuationOf q 843 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause831 (q : Snake 81) (h : Conditions q) : valuation q 813 = false ∨ valuation q 832 = false ∨ valuation q 843 = true := counterClause831 (baseVal q)

theorem counterClause832 (q : Nat → Bool) : valuationOf q 813 = false ∨ valuationOf q 833 = false ∨ valuationOf q 844 = true := by
  have hs : count837 q = (countLit q [-1, -4, -7, -9, -11, -13, -14]) + (countLit q [-16, -18, -19, -21, -22, -24, -25]) := List.countP_append (p := literal q) (l₁ := [-1, -4, -7, -9, -11, -13, -14]) (l₂ := [-16, -18, -19, -21, -22, -24, -25])
  have hm := merge_two (literal (valuationOf q) (813)) (literal (valuationOf q) (833)) (literal (valuationOf q) (844)) (countLit q [-1, -4, -7, -9, -11, -13, -14]) (countLit q [-16, -18, -19, -21, -22, -24, -25]) (count837 q) 4 4 (meaning813 q) (meaning833 q) (meaning844 q) hs
  change valuationOf q 813 = false ∨ valuationOf q 833 = false ∨ valuationOf q 844 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause832 (q : Snake 81) (h : Conditions q) : valuation q 813 = false ∨ valuation q 833 = false ∨ valuation q 844 = true := counterClause832 (baseVal q)

theorem block25 (q : Snake 81) (h : Conditions q) : B112E115.Block25 (valuation q) :=
  ⟨clause801 q h, clause802 q h, clause803 q h, clause804 q h, clause805 q h, clause806 q h, clause807 q h, clause808 q h, clause809 q h, clause810 q h, clause811 q h, clause812 q h, clause813 q h, clause814 q h, clause815 q h, clause816 q h, clause817 q h, clause818 q h, clause819 q h, clause820 q h, clause821 q h, clause822 q h, clause823 q h, clause824 q h, clause825 q h, clause826 q h, clause827 q h, clause828 q h, clause829 q h, clause830 q h, clause831 q h, clause832 q h⟩

end
end Snake9.Regrowth.E112115
