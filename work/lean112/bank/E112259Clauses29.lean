import E112259Semantics
import B112E259Inputs
namespace Snake9.Regrowth.E112259
noncomputable section
local instance blockDec29 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause929 (q : Nat → Bool) : valuationOf q 800 = false ∨ valuationOf q 822 = false ∨ valuationOf q 830 = true := by
  have hs : count827 q = (countLit q [-1, -2, -6, -7, -10, -11, -14]) + (countLit q [-15, -17, -19, -21, -23, -25, -27]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -6, -7, -10, -11, -14]) (l₂ := [-15, -17, -19, -21, -23, -25, -27])
  have hm := merge_two (literal (valuationOf q) (800)) (literal (valuationOf q) (822)) (literal (valuationOf q) (830)) (countLit q [-1, -2, -6, -7, -10, -11, -14]) (countLit q [-15, -17, -19, -21, -23, -25, -27]) (count827 q) 1 3 (meaning800 q) (meaning822 q) (meaning830 q) hs
  change valuationOf q 800 = false ∨ valuationOf q 822 = false ∨ valuationOf q 830 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause929 (q : Snake 81) (h : Conditions q) : valuation q 800 = false ∨ valuation q 822 = false ∨ valuation q 830 = true := counterClause929 (baseVal q)

theorem counterClause930 (q : Nat → Bool) : valuationOf q 800 = false ∨ valuationOf q 823 = false ∨ valuationOf q 831 = true := by
  have hs : count827 q = (countLit q [-1, -2, -6, -7, -10, -11, -14]) + (countLit q [-15, -17, -19, -21, -23, -25, -27]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -6, -7, -10, -11, -14]) (l₂ := [-15, -17, -19, -21, -23, -25, -27])
  have hm := merge_two (literal (valuationOf q) (800)) (literal (valuationOf q) (823)) (literal (valuationOf q) (831)) (countLit q [-1, -2, -6, -7, -10, -11, -14]) (countLit q [-15, -17, -19, -21, -23, -25, -27]) (count827 q) 1 4 (meaning800 q) (meaning823 q) (meaning831 q) hs
  change valuationOf q 800 = false ∨ valuationOf q 823 = false ∨ valuationOf q 831 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause930 (q : Snake 81) (h : Conditions q) : valuation q 800 = false ∨ valuation q 823 = false ∨ valuation q 831 = true := counterClause930 (baseVal q)

theorem counterClause931 (q : Nat → Bool) : valuationOf q 800 = false ∨ valuationOf q 824 = false ∨ valuationOf q 832 = true := by
  have hs : count827 q = (countLit q [-1, -2, -6, -7, -10, -11, -14]) + (countLit q [-15, -17, -19, -21, -23, -25, -27]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -6, -7, -10, -11, -14]) (l₂ := [-15, -17, -19, -21, -23, -25, -27])
  have hm := merge_two (literal (valuationOf q) (800)) (literal (valuationOf q) (824)) (literal (valuationOf q) (832)) (countLit q [-1, -2, -6, -7, -10, -11, -14]) (countLit q [-15, -17, -19, -21, -23, -25, -27]) (count827 q) 1 5 (meaning800 q) (meaning824 q) (meaning832 q) hs
  change valuationOf q 800 = false ∨ valuationOf q 824 = false ∨ valuationOf q 832 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause931 (q : Snake 81) (h : Conditions q) : valuation q 800 = false ∨ valuation q 824 = false ∨ valuation q 832 = true := counterClause931 (baseVal q)

theorem counterClause932 (q : Nat → Bool) : valuationOf q 800 = false ∨ valuationOf q 825 = false ∨ valuationOf q 833 = true := by
  have hs : count827 q = (countLit q [-1, -2, -6, -7, -10, -11, -14]) + (countLit q [-15, -17, -19, -21, -23, -25, -27]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -6, -7, -10, -11, -14]) (l₂ := [-15, -17, -19, -21, -23, -25, -27])
  have hm := merge_two (literal (valuationOf q) (800)) (literal (valuationOf q) (825)) (literal (valuationOf q) (833)) (countLit q [-1, -2, -6, -7, -10, -11, -14]) (countLit q [-15, -17, -19, -21, -23, -25, -27]) (count827 q) 1 6 (meaning800 q) (meaning825 q) (meaning833 q) hs
  change valuationOf q 800 = false ∨ valuationOf q 825 = false ∨ valuationOf q 833 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause932 (q : Snake 81) (h : Conditions q) : valuation q 800 = false ∨ valuation q 825 = false ∨ valuation q 833 = true := counterClause932 (baseVal q)

theorem counterClause933 (q : Nat → Bool) : valuationOf q 801 = false ∨ valuationOf q 828 = true := by
  have hs : count827 q = (countLit q [-1, -2, -6, -7, -10, -11, -14]) + (countLit q [-15, -17, -19, -21, -23, -25, -27]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -6, -7, -10, -11, -14]) (l₂ := [-15, -17, -19, -21, -23, -25, -27])
  have hm := merge_left (literal (valuationOf q) (801)) (literal (valuationOf q) (828)) (countLit q [-1, -2, -6, -7, -10, -11, -14]) (countLit q [-15, -17, -19, -21, -23, -25, -27]) (count827 q) 2 (meaning801 q) (meaning828 q) hs
  change valuationOf q 801 = false ∨ valuationOf q 828 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause933 (q : Snake 81) (h : Conditions q) : valuation q 801 = false ∨ valuation q 828 = true := counterClause933 (baseVal q)

theorem counterClause934 (q : Nat → Bool) : valuationOf q 801 = false ∨ valuationOf q 820 = false ∨ valuationOf q 829 = true := by
  have hs : count827 q = (countLit q [-1, -2, -6, -7, -10, -11, -14]) + (countLit q [-15, -17, -19, -21, -23, -25, -27]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -6, -7, -10, -11, -14]) (l₂ := [-15, -17, -19, -21, -23, -25, -27])
  have hm := merge_two (literal (valuationOf q) (801)) (literal (valuationOf q) (820)) (literal (valuationOf q) (829)) (countLit q [-1, -2, -6, -7, -10, -11, -14]) (countLit q [-15, -17, -19, -21, -23, -25, -27]) (count827 q) 2 1 (meaning801 q) (meaning820 q) (meaning829 q) hs
  change valuationOf q 801 = false ∨ valuationOf q 820 = false ∨ valuationOf q 829 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause934 (q : Snake 81) (h : Conditions q) : valuation q 801 = false ∨ valuation q 820 = false ∨ valuation q 829 = true := counterClause934 (baseVal q)

theorem counterClause935 (q : Nat → Bool) : valuationOf q 801 = false ∨ valuationOf q 821 = false ∨ valuationOf q 830 = true := by
  have hs : count827 q = (countLit q [-1, -2, -6, -7, -10, -11, -14]) + (countLit q [-15, -17, -19, -21, -23, -25, -27]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -6, -7, -10, -11, -14]) (l₂ := [-15, -17, -19, -21, -23, -25, -27])
  have hm := merge_two (literal (valuationOf q) (801)) (literal (valuationOf q) (821)) (literal (valuationOf q) (830)) (countLit q [-1, -2, -6, -7, -10, -11, -14]) (countLit q [-15, -17, -19, -21, -23, -25, -27]) (count827 q) 2 2 (meaning801 q) (meaning821 q) (meaning830 q) hs
  change valuationOf q 801 = false ∨ valuationOf q 821 = false ∨ valuationOf q 830 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause935 (q : Snake 81) (h : Conditions q) : valuation q 801 = false ∨ valuation q 821 = false ∨ valuation q 830 = true := counterClause935 (baseVal q)

theorem counterClause936 (q : Nat → Bool) : valuationOf q 801 = false ∨ valuationOf q 822 = false ∨ valuationOf q 831 = true := by
  have hs : count827 q = (countLit q [-1, -2, -6, -7, -10, -11, -14]) + (countLit q [-15, -17, -19, -21, -23, -25, -27]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -6, -7, -10, -11, -14]) (l₂ := [-15, -17, -19, -21, -23, -25, -27])
  have hm := merge_two (literal (valuationOf q) (801)) (literal (valuationOf q) (822)) (literal (valuationOf q) (831)) (countLit q [-1, -2, -6, -7, -10, -11, -14]) (countLit q [-15, -17, -19, -21, -23, -25, -27]) (count827 q) 2 3 (meaning801 q) (meaning822 q) (meaning831 q) hs
  change valuationOf q 801 = false ∨ valuationOf q 822 = false ∨ valuationOf q 831 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause936 (q : Snake 81) (h : Conditions q) : valuation q 801 = false ∨ valuation q 822 = false ∨ valuation q 831 = true := counterClause936 (baseVal q)

theorem counterClause937 (q : Nat → Bool) : valuationOf q 801 = false ∨ valuationOf q 823 = false ∨ valuationOf q 832 = true := by
  have hs : count827 q = (countLit q [-1, -2, -6, -7, -10, -11, -14]) + (countLit q [-15, -17, -19, -21, -23, -25, -27]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -6, -7, -10, -11, -14]) (l₂ := [-15, -17, -19, -21, -23, -25, -27])
  have hm := merge_two (literal (valuationOf q) (801)) (literal (valuationOf q) (823)) (literal (valuationOf q) (832)) (countLit q [-1, -2, -6, -7, -10, -11, -14]) (countLit q [-15, -17, -19, -21, -23, -25, -27]) (count827 q) 2 4 (meaning801 q) (meaning823 q) (meaning832 q) hs
  change valuationOf q 801 = false ∨ valuationOf q 823 = false ∨ valuationOf q 832 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause937 (q : Snake 81) (h : Conditions q) : valuation q 801 = false ∨ valuation q 823 = false ∨ valuation q 832 = true := counterClause937 (baseVal q)

theorem counterClause938 (q : Nat → Bool) : valuationOf q 801 = false ∨ valuationOf q 824 = false ∨ valuationOf q 833 = true := by
  have hs : count827 q = (countLit q [-1, -2, -6, -7, -10, -11, -14]) + (countLit q [-15, -17, -19, -21, -23, -25, -27]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -6, -7, -10, -11, -14]) (l₂ := [-15, -17, -19, -21, -23, -25, -27])
  have hm := merge_two (literal (valuationOf q) (801)) (literal (valuationOf q) (824)) (literal (valuationOf q) (833)) (countLit q [-1, -2, -6, -7, -10, -11, -14]) (countLit q [-15, -17, -19, -21, -23, -25, -27]) (count827 q) 2 5 (meaning801 q) (meaning824 q) (meaning833 q) hs
  change valuationOf q 801 = false ∨ valuationOf q 824 = false ∨ valuationOf q 833 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause938 (q : Snake 81) (h : Conditions q) : valuation q 801 = false ∨ valuation q 824 = false ∨ valuation q 833 = true := counterClause938 (baseVal q)

theorem counterClause939 (q : Nat → Bool) : valuationOf q 801 = false ∨ valuationOf q 825 = false ∨ valuationOf q 834 = true := by
  have hs : count827 q = (countLit q [-1, -2, -6, -7, -10, -11, -14]) + (countLit q [-15, -17, -19, -21, -23, -25, -27]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -6, -7, -10, -11, -14]) (l₂ := [-15, -17, -19, -21, -23, -25, -27])
  have hm := merge_two (literal (valuationOf q) (801)) (literal (valuationOf q) (825)) (literal (valuationOf q) (834)) (countLit q [-1, -2, -6, -7, -10, -11, -14]) (countLit q [-15, -17, -19, -21, -23, -25, -27]) (count827 q) 2 6 (meaning801 q) (meaning825 q) (meaning834 q) hs
  change valuationOf q 801 = false ∨ valuationOf q 825 = false ∨ valuationOf q 834 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause939 (q : Snake 81) (h : Conditions q) : valuation q 801 = false ∨ valuation q 825 = false ∨ valuation q 834 = true := counterClause939 (baseVal q)

theorem counterClause940 (q : Nat → Bool) : valuationOf q 802 = false ∨ valuationOf q 829 = true := by
  have hs : count827 q = (countLit q [-1, -2, -6, -7, -10, -11, -14]) + (countLit q [-15, -17, -19, -21, -23, -25, -27]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -6, -7, -10, -11, -14]) (l₂ := [-15, -17, -19, -21, -23, -25, -27])
  have hm := merge_left (literal (valuationOf q) (802)) (literal (valuationOf q) (829)) (countLit q [-1, -2, -6, -7, -10, -11, -14]) (countLit q [-15, -17, -19, -21, -23, -25, -27]) (count827 q) 3 (meaning802 q) (meaning829 q) hs
  change valuationOf q 802 = false ∨ valuationOf q 829 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause940 (q : Snake 81) (h : Conditions q) : valuation q 802 = false ∨ valuation q 829 = true := counterClause940 (baseVal q)

theorem counterClause941 (q : Nat → Bool) : valuationOf q 802 = false ∨ valuationOf q 820 = false ∨ valuationOf q 830 = true := by
  have hs : count827 q = (countLit q [-1, -2, -6, -7, -10, -11, -14]) + (countLit q [-15, -17, -19, -21, -23, -25, -27]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -6, -7, -10, -11, -14]) (l₂ := [-15, -17, -19, -21, -23, -25, -27])
  have hm := merge_two (literal (valuationOf q) (802)) (literal (valuationOf q) (820)) (literal (valuationOf q) (830)) (countLit q [-1, -2, -6, -7, -10, -11, -14]) (countLit q [-15, -17, -19, -21, -23, -25, -27]) (count827 q) 3 1 (meaning802 q) (meaning820 q) (meaning830 q) hs
  change valuationOf q 802 = false ∨ valuationOf q 820 = false ∨ valuationOf q 830 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause941 (q : Snake 81) (h : Conditions q) : valuation q 802 = false ∨ valuation q 820 = false ∨ valuation q 830 = true := counterClause941 (baseVal q)

theorem counterClause942 (q : Nat → Bool) : valuationOf q 802 = false ∨ valuationOf q 821 = false ∨ valuationOf q 831 = true := by
  have hs : count827 q = (countLit q [-1, -2, -6, -7, -10, -11, -14]) + (countLit q [-15, -17, -19, -21, -23, -25, -27]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -6, -7, -10, -11, -14]) (l₂ := [-15, -17, -19, -21, -23, -25, -27])
  have hm := merge_two (literal (valuationOf q) (802)) (literal (valuationOf q) (821)) (literal (valuationOf q) (831)) (countLit q [-1, -2, -6, -7, -10, -11, -14]) (countLit q [-15, -17, -19, -21, -23, -25, -27]) (count827 q) 3 2 (meaning802 q) (meaning821 q) (meaning831 q) hs
  change valuationOf q 802 = false ∨ valuationOf q 821 = false ∨ valuationOf q 831 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause942 (q : Snake 81) (h : Conditions q) : valuation q 802 = false ∨ valuation q 821 = false ∨ valuation q 831 = true := counterClause942 (baseVal q)

theorem counterClause943 (q : Nat → Bool) : valuationOf q 802 = false ∨ valuationOf q 822 = false ∨ valuationOf q 832 = true := by
  have hs : count827 q = (countLit q [-1, -2, -6, -7, -10, -11, -14]) + (countLit q [-15, -17, -19, -21, -23, -25, -27]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -6, -7, -10, -11, -14]) (l₂ := [-15, -17, -19, -21, -23, -25, -27])
  have hm := merge_two (literal (valuationOf q) (802)) (literal (valuationOf q) (822)) (literal (valuationOf q) (832)) (countLit q [-1, -2, -6, -7, -10, -11, -14]) (countLit q [-15, -17, -19, -21, -23, -25, -27]) (count827 q) 3 3 (meaning802 q) (meaning822 q) (meaning832 q) hs
  change valuationOf q 802 = false ∨ valuationOf q 822 = false ∨ valuationOf q 832 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause943 (q : Snake 81) (h : Conditions q) : valuation q 802 = false ∨ valuation q 822 = false ∨ valuation q 832 = true := counterClause943 (baseVal q)

theorem counterClause944 (q : Nat → Bool) : valuationOf q 802 = false ∨ valuationOf q 823 = false ∨ valuationOf q 833 = true := by
  have hs : count827 q = (countLit q [-1, -2, -6, -7, -10, -11, -14]) + (countLit q [-15, -17, -19, -21, -23, -25, -27]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -6, -7, -10, -11, -14]) (l₂ := [-15, -17, -19, -21, -23, -25, -27])
  have hm := merge_two (literal (valuationOf q) (802)) (literal (valuationOf q) (823)) (literal (valuationOf q) (833)) (countLit q [-1, -2, -6, -7, -10, -11, -14]) (countLit q [-15, -17, -19, -21, -23, -25, -27]) (count827 q) 3 4 (meaning802 q) (meaning823 q) (meaning833 q) hs
  change valuationOf q 802 = false ∨ valuationOf q 823 = false ∨ valuationOf q 833 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause944 (q : Snake 81) (h : Conditions q) : valuation q 802 = false ∨ valuation q 823 = false ∨ valuation q 833 = true := counterClause944 (baseVal q)

theorem counterClause945 (q : Nat → Bool) : valuationOf q 802 = false ∨ valuationOf q 824 = false ∨ valuationOf q 834 = true := by
  have hs : count827 q = (countLit q [-1, -2, -6, -7, -10, -11, -14]) + (countLit q [-15, -17, -19, -21, -23, -25, -27]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -6, -7, -10, -11, -14]) (l₂ := [-15, -17, -19, -21, -23, -25, -27])
  have hm := merge_two (literal (valuationOf q) (802)) (literal (valuationOf q) (824)) (literal (valuationOf q) (834)) (countLit q [-1, -2, -6, -7, -10, -11, -14]) (countLit q [-15, -17, -19, -21, -23, -25, -27]) (count827 q) 3 5 (meaning802 q) (meaning824 q) (meaning834 q) hs
  change valuationOf q 802 = false ∨ valuationOf q 824 = false ∨ valuationOf q 834 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause945 (q : Snake 81) (h : Conditions q) : valuation q 802 = false ∨ valuation q 824 = false ∨ valuation q 834 = true := counterClause945 (baseVal q)

theorem counterClause946 (q : Nat → Bool) : valuationOf q 802 = false ∨ valuationOf q 825 = false ∨ valuationOf q 835 = true := by
  have hs : count827 q = (countLit q [-1, -2, -6, -7, -10, -11, -14]) + (countLit q [-15, -17, -19, -21, -23, -25, -27]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -6, -7, -10, -11, -14]) (l₂ := [-15, -17, -19, -21, -23, -25, -27])
  have hm := merge_two (literal (valuationOf q) (802)) (literal (valuationOf q) (825)) (literal (valuationOf q) (835)) (countLit q [-1, -2, -6, -7, -10, -11, -14]) (countLit q [-15, -17, -19, -21, -23, -25, -27]) (count827 q) 3 6 (meaning802 q) (meaning825 q) (meaning835 q) hs
  change valuationOf q 802 = false ∨ valuationOf q 825 = false ∨ valuationOf q 835 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause946 (q : Snake 81) (h : Conditions q) : valuation q 802 = false ∨ valuation q 825 = false ∨ valuation q 835 = true := counterClause946 (baseVal q)

theorem counterClause947 (q : Nat → Bool) : valuationOf q 803 = false ∨ valuationOf q 830 = true := by
  have hs : count827 q = (countLit q [-1, -2, -6, -7, -10, -11, -14]) + (countLit q [-15, -17, -19, -21, -23, -25, -27]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -6, -7, -10, -11, -14]) (l₂ := [-15, -17, -19, -21, -23, -25, -27])
  have hm := merge_left (literal (valuationOf q) (803)) (literal (valuationOf q) (830)) (countLit q [-1, -2, -6, -7, -10, -11, -14]) (countLit q [-15, -17, -19, -21, -23, -25, -27]) (count827 q) 4 (meaning803 q) (meaning830 q) hs
  change valuationOf q 803 = false ∨ valuationOf q 830 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause947 (q : Snake 81) (h : Conditions q) : valuation q 803 = false ∨ valuation q 830 = true := counterClause947 (baseVal q)

theorem counterClause948 (q : Nat → Bool) : valuationOf q 803 = false ∨ valuationOf q 820 = false ∨ valuationOf q 831 = true := by
  have hs : count827 q = (countLit q [-1, -2, -6, -7, -10, -11, -14]) + (countLit q [-15, -17, -19, -21, -23, -25, -27]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -6, -7, -10, -11, -14]) (l₂ := [-15, -17, -19, -21, -23, -25, -27])
  have hm := merge_two (literal (valuationOf q) (803)) (literal (valuationOf q) (820)) (literal (valuationOf q) (831)) (countLit q [-1, -2, -6, -7, -10, -11, -14]) (countLit q [-15, -17, -19, -21, -23, -25, -27]) (count827 q) 4 1 (meaning803 q) (meaning820 q) (meaning831 q) hs
  change valuationOf q 803 = false ∨ valuationOf q 820 = false ∨ valuationOf q 831 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause948 (q : Snake 81) (h : Conditions q) : valuation q 803 = false ∨ valuation q 820 = false ∨ valuation q 831 = true := counterClause948 (baseVal q)

theorem counterClause949 (q : Nat → Bool) : valuationOf q 803 = false ∨ valuationOf q 821 = false ∨ valuationOf q 832 = true := by
  have hs : count827 q = (countLit q [-1, -2, -6, -7, -10, -11, -14]) + (countLit q [-15, -17, -19, -21, -23, -25, -27]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -6, -7, -10, -11, -14]) (l₂ := [-15, -17, -19, -21, -23, -25, -27])
  have hm := merge_two (literal (valuationOf q) (803)) (literal (valuationOf q) (821)) (literal (valuationOf q) (832)) (countLit q [-1, -2, -6, -7, -10, -11, -14]) (countLit q [-15, -17, -19, -21, -23, -25, -27]) (count827 q) 4 2 (meaning803 q) (meaning821 q) (meaning832 q) hs
  change valuationOf q 803 = false ∨ valuationOf q 821 = false ∨ valuationOf q 832 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause949 (q : Snake 81) (h : Conditions q) : valuation q 803 = false ∨ valuation q 821 = false ∨ valuation q 832 = true := counterClause949 (baseVal q)

theorem counterClause950 (q : Nat → Bool) : valuationOf q 803 = false ∨ valuationOf q 822 = false ∨ valuationOf q 833 = true := by
  have hs : count827 q = (countLit q [-1, -2, -6, -7, -10, -11, -14]) + (countLit q [-15, -17, -19, -21, -23, -25, -27]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -6, -7, -10, -11, -14]) (l₂ := [-15, -17, -19, -21, -23, -25, -27])
  have hm := merge_two (literal (valuationOf q) (803)) (literal (valuationOf q) (822)) (literal (valuationOf q) (833)) (countLit q [-1, -2, -6, -7, -10, -11, -14]) (countLit q [-15, -17, -19, -21, -23, -25, -27]) (count827 q) 4 3 (meaning803 q) (meaning822 q) (meaning833 q) hs
  change valuationOf q 803 = false ∨ valuationOf q 822 = false ∨ valuationOf q 833 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause950 (q : Snake 81) (h : Conditions q) : valuation q 803 = false ∨ valuation q 822 = false ∨ valuation q 833 = true := counterClause950 (baseVal q)

theorem counterClause951 (q : Nat → Bool) : valuationOf q 803 = false ∨ valuationOf q 823 = false ∨ valuationOf q 834 = true := by
  have hs : count827 q = (countLit q [-1, -2, -6, -7, -10, -11, -14]) + (countLit q [-15, -17, -19, -21, -23, -25, -27]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -6, -7, -10, -11, -14]) (l₂ := [-15, -17, -19, -21, -23, -25, -27])
  have hm := merge_two (literal (valuationOf q) (803)) (literal (valuationOf q) (823)) (literal (valuationOf q) (834)) (countLit q [-1, -2, -6, -7, -10, -11, -14]) (countLit q [-15, -17, -19, -21, -23, -25, -27]) (count827 q) 4 4 (meaning803 q) (meaning823 q) (meaning834 q) hs
  change valuationOf q 803 = false ∨ valuationOf q 823 = false ∨ valuationOf q 834 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause951 (q : Snake 81) (h : Conditions q) : valuation q 803 = false ∨ valuation q 823 = false ∨ valuation q 834 = true := counterClause951 (baseVal q)

theorem counterClause952 (q : Nat → Bool) : valuationOf q 803 = false ∨ valuationOf q 824 = false ∨ valuationOf q 835 = true := by
  have hs : count827 q = (countLit q [-1, -2, -6, -7, -10, -11, -14]) + (countLit q [-15, -17, -19, -21, -23, -25, -27]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -6, -7, -10, -11, -14]) (l₂ := [-15, -17, -19, -21, -23, -25, -27])
  have hm := merge_two (literal (valuationOf q) (803)) (literal (valuationOf q) (824)) (literal (valuationOf q) (835)) (countLit q [-1, -2, -6, -7, -10, -11, -14]) (countLit q [-15, -17, -19, -21, -23, -25, -27]) (count827 q) 4 5 (meaning803 q) (meaning824 q) (meaning835 q) hs
  change valuationOf q 803 = false ∨ valuationOf q 824 = false ∨ valuationOf q 835 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause952 (q : Snake 81) (h : Conditions q) : valuation q 803 = false ∨ valuation q 824 = false ∨ valuation q 835 = true := counterClause952 (baseVal q)

theorem counterClause953 (q : Nat → Bool) : valuationOf q 803 = false ∨ valuationOf q 825 = false ∨ valuationOf q 836 = true := by
  have hs : count827 q = (countLit q [-1, -2, -6, -7, -10, -11, -14]) + (countLit q [-15, -17, -19, -21, -23, -25, -27]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -6, -7, -10, -11, -14]) (l₂ := [-15, -17, -19, -21, -23, -25, -27])
  have hm := merge_two (literal (valuationOf q) (803)) (literal (valuationOf q) (825)) (literal (valuationOf q) (836)) (countLit q [-1, -2, -6, -7, -10, -11, -14]) (countLit q [-15, -17, -19, -21, -23, -25, -27]) (count827 q) 4 6 (meaning803 q) (meaning825 q) (meaning836 q) hs
  change valuationOf q 803 = false ∨ valuationOf q 825 = false ∨ valuationOf q 836 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause953 (q : Snake 81) (h : Conditions q) : valuation q 803 = false ∨ valuation q 825 = false ∨ valuation q 836 = true := counterClause953 (baseVal q)

theorem counterClause954 (q : Nat → Bool) : valuationOf q 804 = false ∨ valuationOf q 831 = true := by
  have hs : count827 q = (countLit q [-1, -2, -6, -7, -10, -11, -14]) + (countLit q [-15, -17, -19, -21, -23, -25, -27]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -6, -7, -10, -11, -14]) (l₂ := [-15, -17, -19, -21, -23, -25, -27])
  have hm := merge_left (literal (valuationOf q) (804)) (literal (valuationOf q) (831)) (countLit q [-1, -2, -6, -7, -10, -11, -14]) (countLit q [-15, -17, -19, -21, -23, -25, -27]) (count827 q) 5 (meaning804 q) (meaning831 q) hs
  change valuationOf q 804 = false ∨ valuationOf q 831 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause954 (q : Snake 81) (h : Conditions q) : valuation q 804 = false ∨ valuation q 831 = true := counterClause954 (baseVal q)

theorem counterClause955 (q : Nat → Bool) : valuationOf q 804 = false ∨ valuationOf q 820 = false ∨ valuationOf q 832 = true := by
  have hs : count827 q = (countLit q [-1, -2, -6, -7, -10, -11, -14]) + (countLit q [-15, -17, -19, -21, -23, -25, -27]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -6, -7, -10, -11, -14]) (l₂ := [-15, -17, -19, -21, -23, -25, -27])
  have hm := merge_two (literal (valuationOf q) (804)) (literal (valuationOf q) (820)) (literal (valuationOf q) (832)) (countLit q [-1, -2, -6, -7, -10, -11, -14]) (countLit q [-15, -17, -19, -21, -23, -25, -27]) (count827 q) 5 1 (meaning804 q) (meaning820 q) (meaning832 q) hs
  change valuationOf q 804 = false ∨ valuationOf q 820 = false ∨ valuationOf q 832 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause955 (q : Snake 81) (h : Conditions q) : valuation q 804 = false ∨ valuation q 820 = false ∨ valuation q 832 = true := counterClause955 (baseVal q)

theorem counterClause956 (q : Nat → Bool) : valuationOf q 804 = false ∨ valuationOf q 821 = false ∨ valuationOf q 833 = true := by
  have hs : count827 q = (countLit q [-1, -2, -6, -7, -10, -11, -14]) + (countLit q [-15, -17, -19, -21, -23, -25, -27]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -6, -7, -10, -11, -14]) (l₂ := [-15, -17, -19, -21, -23, -25, -27])
  have hm := merge_two (literal (valuationOf q) (804)) (literal (valuationOf q) (821)) (literal (valuationOf q) (833)) (countLit q [-1, -2, -6, -7, -10, -11, -14]) (countLit q [-15, -17, -19, -21, -23, -25, -27]) (count827 q) 5 2 (meaning804 q) (meaning821 q) (meaning833 q) hs
  change valuationOf q 804 = false ∨ valuationOf q 821 = false ∨ valuationOf q 833 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause956 (q : Snake 81) (h : Conditions q) : valuation q 804 = false ∨ valuation q 821 = false ∨ valuation q 833 = true := counterClause956 (baseVal q)

theorem counterClause957 (q : Nat → Bool) : valuationOf q 804 = false ∨ valuationOf q 822 = false ∨ valuationOf q 834 = true := by
  have hs : count827 q = (countLit q [-1, -2, -6, -7, -10, -11, -14]) + (countLit q [-15, -17, -19, -21, -23, -25, -27]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -6, -7, -10, -11, -14]) (l₂ := [-15, -17, -19, -21, -23, -25, -27])
  have hm := merge_two (literal (valuationOf q) (804)) (literal (valuationOf q) (822)) (literal (valuationOf q) (834)) (countLit q [-1, -2, -6, -7, -10, -11, -14]) (countLit q [-15, -17, -19, -21, -23, -25, -27]) (count827 q) 5 3 (meaning804 q) (meaning822 q) (meaning834 q) hs
  change valuationOf q 804 = false ∨ valuationOf q 822 = false ∨ valuationOf q 834 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause957 (q : Snake 81) (h : Conditions q) : valuation q 804 = false ∨ valuation q 822 = false ∨ valuation q 834 = true := counterClause957 (baseVal q)

theorem counterClause958 (q : Nat → Bool) : valuationOf q 804 = false ∨ valuationOf q 823 = false ∨ valuationOf q 835 = true := by
  have hs : count827 q = (countLit q [-1, -2, -6, -7, -10, -11, -14]) + (countLit q [-15, -17, -19, -21, -23, -25, -27]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -6, -7, -10, -11, -14]) (l₂ := [-15, -17, -19, -21, -23, -25, -27])
  have hm := merge_two (literal (valuationOf q) (804)) (literal (valuationOf q) (823)) (literal (valuationOf q) (835)) (countLit q [-1, -2, -6, -7, -10, -11, -14]) (countLit q [-15, -17, -19, -21, -23, -25, -27]) (count827 q) 5 4 (meaning804 q) (meaning823 q) (meaning835 q) hs
  change valuationOf q 804 = false ∨ valuationOf q 823 = false ∨ valuationOf q 835 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause958 (q : Snake 81) (h : Conditions q) : valuation q 804 = false ∨ valuation q 823 = false ∨ valuation q 835 = true := counterClause958 (baseVal q)

theorem counterClause959 (q : Nat → Bool) : valuationOf q 804 = false ∨ valuationOf q 824 = false ∨ valuationOf q 836 = true := by
  have hs : count827 q = (countLit q [-1, -2, -6, -7, -10, -11, -14]) + (countLit q [-15, -17, -19, -21, -23, -25, -27]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -6, -7, -10, -11, -14]) (l₂ := [-15, -17, -19, -21, -23, -25, -27])
  have hm := merge_two (literal (valuationOf q) (804)) (literal (valuationOf q) (824)) (literal (valuationOf q) (836)) (countLit q [-1, -2, -6, -7, -10, -11, -14]) (countLit q [-15, -17, -19, -21, -23, -25, -27]) (count827 q) 5 5 (meaning804 q) (meaning824 q) (meaning836 q) hs
  change valuationOf q 804 = false ∨ valuationOf q 824 = false ∨ valuationOf q 836 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause959 (q : Snake 81) (h : Conditions q) : valuation q 804 = false ∨ valuation q 824 = false ∨ valuation q 836 = true := counterClause959 (baseVal q)

theorem counterClause960 (q : Nat → Bool) : valuationOf q 804 = false ∨ valuationOf q 825 = false ∨ valuationOf q 837 = true := by
  have hs : count827 q = (countLit q [-1, -2, -6, -7, -10, -11, -14]) + (countLit q [-15, -17, -19, -21, -23, -25, -27]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -6, -7, -10, -11, -14]) (l₂ := [-15, -17, -19, -21, -23, -25, -27])
  have hm := merge_two (literal (valuationOf q) (804)) (literal (valuationOf q) (825)) (literal (valuationOf q) (837)) (countLit q [-1, -2, -6, -7, -10, -11, -14]) (countLit q [-15, -17, -19, -21, -23, -25, -27]) (count827 q) 5 6 (meaning804 q) (meaning825 q) (meaning837 q) hs
  change valuationOf q 804 = false ∨ valuationOf q 825 = false ∨ valuationOf q 837 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause960 (q : Snake 81) (h : Conditions q) : valuation q 804 = false ∨ valuation q 825 = false ∨ valuation q 837 = true := counterClause960 (baseVal q)

theorem block29 (q : Snake 81) (h : Conditions q) : B112E259.Block29 (valuation q) :=
  ⟨clause929 q h, clause930 q h, clause931 q h, clause932 q h, clause933 q h, clause934 q h, clause935 q h, clause936 q h, clause937 q h, clause938 q h, clause939 q h, clause940 q h, clause941 q h, clause942 q h, clause943 q h, clause944 q h, clause945 q h, clause946 q h, clause947 q h, clause948 q h, clause949 q h, clause950 q h, clause951 q h, clause952 q h, clause953 q h, clause954 q h, clause955 q h, clause956 q h, clause957 q h, clause958 q h, clause959 q h, clause960 q h⟩

end
end Snake9.Regrowth.E112259
