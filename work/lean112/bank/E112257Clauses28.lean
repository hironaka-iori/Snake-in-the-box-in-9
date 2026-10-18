import E112257Semantics
import B112E257Inputs
namespace Snake9.Regrowth.E112257
noncomputable section
local instance blockDec28 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause897 (q : Nat → Bool) : valuationOf q 801 = false ∨ valuationOf q 822 = false ∨ valuationOf q 831 = true := by
  have hs : count827 q = (countLit q [-1, -2, -4, -6, -7, -11, -12]) + (countLit q [-15, -16, -19, -21, -23, -26, -28]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -4, -6, -7, -11, -12]) (l₂ := [-15, -16, -19, -21, -23, -26, -28])
  have hm := merge_two (literal (valuationOf q) (801)) (literal (valuationOf q) (822)) (literal (valuationOf q) (831)) (countLit q [-1, -2, -4, -6, -7, -11, -12]) (countLit q [-15, -16, -19, -21, -23, -26, -28]) (count827 q) 2 3 (meaning801 q) (meaning822 q) (meaning831 q) hs
  change valuationOf q 801 = false ∨ valuationOf q 822 = false ∨ valuationOf q 831 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause897 (q : Snake 81) (h : Conditions q) : valuation q 801 = false ∨ valuation q 822 = false ∨ valuation q 831 = true := counterClause897 (baseVal q)

theorem counterClause898 (q : Nat → Bool) : valuationOf q 801 = false ∨ valuationOf q 823 = false ∨ valuationOf q 832 = true := by
  have hs : count827 q = (countLit q [-1, -2, -4, -6, -7, -11, -12]) + (countLit q [-15, -16, -19, -21, -23, -26, -28]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -4, -6, -7, -11, -12]) (l₂ := [-15, -16, -19, -21, -23, -26, -28])
  have hm := merge_two (literal (valuationOf q) (801)) (literal (valuationOf q) (823)) (literal (valuationOf q) (832)) (countLit q [-1, -2, -4, -6, -7, -11, -12]) (countLit q [-15, -16, -19, -21, -23, -26, -28]) (count827 q) 2 4 (meaning801 q) (meaning823 q) (meaning832 q) hs
  change valuationOf q 801 = false ∨ valuationOf q 823 = false ∨ valuationOf q 832 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause898 (q : Snake 81) (h : Conditions q) : valuation q 801 = false ∨ valuation q 823 = false ∨ valuation q 832 = true := counterClause898 (baseVal q)

theorem counterClause899 (q : Nat → Bool) : valuationOf q 801 = false ∨ valuationOf q 824 = false ∨ valuationOf q 833 = true := by
  have hs : count827 q = (countLit q [-1, -2, -4, -6, -7, -11, -12]) + (countLit q [-15, -16, -19, -21, -23, -26, -28]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -4, -6, -7, -11, -12]) (l₂ := [-15, -16, -19, -21, -23, -26, -28])
  have hm := merge_two (literal (valuationOf q) (801)) (literal (valuationOf q) (824)) (literal (valuationOf q) (833)) (countLit q [-1, -2, -4, -6, -7, -11, -12]) (countLit q [-15, -16, -19, -21, -23, -26, -28]) (count827 q) 2 5 (meaning801 q) (meaning824 q) (meaning833 q) hs
  change valuationOf q 801 = false ∨ valuationOf q 824 = false ∨ valuationOf q 833 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause899 (q : Snake 81) (h : Conditions q) : valuation q 801 = false ∨ valuation q 824 = false ∨ valuation q 833 = true := counterClause899 (baseVal q)

theorem counterClause900 (q : Nat → Bool) : valuationOf q 801 = false ∨ valuationOf q 825 = false ∨ valuationOf q 834 = true := by
  have hs : count827 q = (countLit q [-1, -2, -4, -6, -7, -11, -12]) + (countLit q [-15, -16, -19, -21, -23, -26, -28]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -4, -6, -7, -11, -12]) (l₂ := [-15, -16, -19, -21, -23, -26, -28])
  have hm := merge_two (literal (valuationOf q) (801)) (literal (valuationOf q) (825)) (literal (valuationOf q) (834)) (countLit q [-1, -2, -4, -6, -7, -11, -12]) (countLit q [-15, -16, -19, -21, -23, -26, -28]) (count827 q) 2 6 (meaning801 q) (meaning825 q) (meaning834 q) hs
  change valuationOf q 801 = false ∨ valuationOf q 825 = false ∨ valuationOf q 834 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause900 (q : Snake 81) (h : Conditions q) : valuation q 801 = false ∨ valuation q 825 = false ∨ valuation q 834 = true := counterClause900 (baseVal q)

theorem counterClause901 (q : Nat → Bool) : valuationOf q 802 = false ∨ valuationOf q 829 = true := by
  have hs : count827 q = (countLit q [-1, -2, -4, -6, -7, -11, -12]) + (countLit q [-15, -16, -19, -21, -23, -26, -28]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -4, -6, -7, -11, -12]) (l₂ := [-15, -16, -19, -21, -23, -26, -28])
  have hm := merge_left (literal (valuationOf q) (802)) (literal (valuationOf q) (829)) (countLit q [-1, -2, -4, -6, -7, -11, -12]) (countLit q [-15, -16, -19, -21, -23, -26, -28]) (count827 q) 3 (meaning802 q) (meaning829 q) hs
  change valuationOf q 802 = false ∨ valuationOf q 829 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause901 (q : Snake 81) (h : Conditions q) : valuation q 802 = false ∨ valuation q 829 = true := counterClause901 (baseVal q)

theorem counterClause902 (q : Nat → Bool) : valuationOf q 802 = false ∨ valuationOf q 820 = false ∨ valuationOf q 830 = true := by
  have hs : count827 q = (countLit q [-1, -2, -4, -6, -7, -11, -12]) + (countLit q [-15, -16, -19, -21, -23, -26, -28]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -4, -6, -7, -11, -12]) (l₂ := [-15, -16, -19, -21, -23, -26, -28])
  have hm := merge_two (literal (valuationOf q) (802)) (literal (valuationOf q) (820)) (literal (valuationOf q) (830)) (countLit q [-1, -2, -4, -6, -7, -11, -12]) (countLit q [-15, -16, -19, -21, -23, -26, -28]) (count827 q) 3 1 (meaning802 q) (meaning820 q) (meaning830 q) hs
  change valuationOf q 802 = false ∨ valuationOf q 820 = false ∨ valuationOf q 830 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause902 (q : Snake 81) (h : Conditions q) : valuation q 802 = false ∨ valuation q 820 = false ∨ valuation q 830 = true := counterClause902 (baseVal q)

theorem counterClause903 (q : Nat → Bool) : valuationOf q 802 = false ∨ valuationOf q 821 = false ∨ valuationOf q 831 = true := by
  have hs : count827 q = (countLit q [-1, -2, -4, -6, -7, -11, -12]) + (countLit q [-15, -16, -19, -21, -23, -26, -28]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -4, -6, -7, -11, -12]) (l₂ := [-15, -16, -19, -21, -23, -26, -28])
  have hm := merge_two (literal (valuationOf q) (802)) (literal (valuationOf q) (821)) (literal (valuationOf q) (831)) (countLit q [-1, -2, -4, -6, -7, -11, -12]) (countLit q [-15, -16, -19, -21, -23, -26, -28]) (count827 q) 3 2 (meaning802 q) (meaning821 q) (meaning831 q) hs
  change valuationOf q 802 = false ∨ valuationOf q 821 = false ∨ valuationOf q 831 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause903 (q : Snake 81) (h : Conditions q) : valuation q 802 = false ∨ valuation q 821 = false ∨ valuation q 831 = true := counterClause903 (baseVal q)

theorem counterClause904 (q : Nat → Bool) : valuationOf q 802 = false ∨ valuationOf q 822 = false ∨ valuationOf q 832 = true := by
  have hs : count827 q = (countLit q [-1, -2, -4, -6, -7, -11, -12]) + (countLit q [-15, -16, -19, -21, -23, -26, -28]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -4, -6, -7, -11, -12]) (l₂ := [-15, -16, -19, -21, -23, -26, -28])
  have hm := merge_two (literal (valuationOf q) (802)) (literal (valuationOf q) (822)) (literal (valuationOf q) (832)) (countLit q [-1, -2, -4, -6, -7, -11, -12]) (countLit q [-15, -16, -19, -21, -23, -26, -28]) (count827 q) 3 3 (meaning802 q) (meaning822 q) (meaning832 q) hs
  change valuationOf q 802 = false ∨ valuationOf q 822 = false ∨ valuationOf q 832 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause904 (q : Snake 81) (h : Conditions q) : valuation q 802 = false ∨ valuation q 822 = false ∨ valuation q 832 = true := counterClause904 (baseVal q)

theorem counterClause905 (q : Nat → Bool) : valuationOf q 802 = false ∨ valuationOf q 823 = false ∨ valuationOf q 833 = true := by
  have hs : count827 q = (countLit q [-1, -2, -4, -6, -7, -11, -12]) + (countLit q [-15, -16, -19, -21, -23, -26, -28]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -4, -6, -7, -11, -12]) (l₂ := [-15, -16, -19, -21, -23, -26, -28])
  have hm := merge_two (literal (valuationOf q) (802)) (literal (valuationOf q) (823)) (literal (valuationOf q) (833)) (countLit q [-1, -2, -4, -6, -7, -11, -12]) (countLit q [-15, -16, -19, -21, -23, -26, -28]) (count827 q) 3 4 (meaning802 q) (meaning823 q) (meaning833 q) hs
  change valuationOf q 802 = false ∨ valuationOf q 823 = false ∨ valuationOf q 833 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause905 (q : Snake 81) (h : Conditions q) : valuation q 802 = false ∨ valuation q 823 = false ∨ valuation q 833 = true := counterClause905 (baseVal q)

theorem counterClause906 (q : Nat → Bool) : valuationOf q 802 = false ∨ valuationOf q 824 = false ∨ valuationOf q 834 = true := by
  have hs : count827 q = (countLit q [-1, -2, -4, -6, -7, -11, -12]) + (countLit q [-15, -16, -19, -21, -23, -26, -28]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -4, -6, -7, -11, -12]) (l₂ := [-15, -16, -19, -21, -23, -26, -28])
  have hm := merge_two (literal (valuationOf q) (802)) (literal (valuationOf q) (824)) (literal (valuationOf q) (834)) (countLit q [-1, -2, -4, -6, -7, -11, -12]) (countLit q [-15, -16, -19, -21, -23, -26, -28]) (count827 q) 3 5 (meaning802 q) (meaning824 q) (meaning834 q) hs
  change valuationOf q 802 = false ∨ valuationOf q 824 = false ∨ valuationOf q 834 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause906 (q : Snake 81) (h : Conditions q) : valuation q 802 = false ∨ valuation q 824 = false ∨ valuation q 834 = true := counterClause906 (baseVal q)

theorem counterClause907 (q : Nat → Bool) : valuationOf q 802 = false ∨ valuationOf q 825 = false ∨ valuationOf q 835 = true := by
  have hs : count827 q = (countLit q [-1, -2, -4, -6, -7, -11, -12]) + (countLit q [-15, -16, -19, -21, -23, -26, -28]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -4, -6, -7, -11, -12]) (l₂ := [-15, -16, -19, -21, -23, -26, -28])
  have hm := merge_two (literal (valuationOf q) (802)) (literal (valuationOf q) (825)) (literal (valuationOf q) (835)) (countLit q [-1, -2, -4, -6, -7, -11, -12]) (countLit q [-15, -16, -19, -21, -23, -26, -28]) (count827 q) 3 6 (meaning802 q) (meaning825 q) (meaning835 q) hs
  change valuationOf q 802 = false ∨ valuationOf q 825 = false ∨ valuationOf q 835 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause907 (q : Snake 81) (h : Conditions q) : valuation q 802 = false ∨ valuation q 825 = false ∨ valuation q 835 = true := counterClause907 (baseVal q)

theorem counterClause908 (q : Nat → Bool) : valuationOf q 802 = false ∨ valuationOf q 826 = false ∨ valuationOf q 836 = true := by
  have hs : count827 q = (countLit q [-1, -2, -4, -6, -7, -11, -12]) + (countLit q [-15, -16, -19, -21, -23, -26, -28]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -4, -6, -7, -11, -12]) (l₂ := [-15, -16, -19, -21, -23, -26, -28])
  have hm := merge_two (literal (valuationOf q) (802)) (literal (valuationOf q) (826)) (literal (valuationOf q) (836)) (countLit q [-1, -2, -4, -6, -7, -11, -12]) (countLit q [-15, -16, -19, -21, -23, -26, -28]) (count827 q) 3 7 (meaning802 q) (meaning826 q) (meaning836 q) hs
  change valuationOf q 802 = false ∨ valuationOf q 826 = false ∨ valuationOf q 836 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause908 (q : Snake 81) (h : Conditions q) : valuation q 802 = false ∨ valuation q 826 = false ∨ valuation q 836 = true := counterClause908 (baseVal q)

theorem counterClause909 (q : Nat → Bool) : valuationOf q 803 = false ∨ valuationOf q 830 = true := by
  have hs : count827 q = (countLit q [-1, -2, -4, -6, -7, -11, -12]) + (countLit q [-15, -16, -19, -21, -23, -26, -28]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -4, -6, -7, -11, -12]) (l₂ := [-15, -16, -19, -21, -23, -26, -28])
  have hm := merge_left (literal (valuationOf q) (803)) (literal (valuationOf q) (830)) (countLit q [-1, -2, -4, -6, -7, -11, -12]) (countLit q [-15, -16, -19, -21, -23, -26, -28]) (count827 q) 4 (meaning803 q) (meaning830 q) hs
  change valuationOf q 803 = false ∨ valuationOf q 830 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause909 (q : Snake 81) (h : Conditions q) : valuation q 803 = false ∨ valuation q 830 = true := counterClause909 (baseVal q)

theorem counterClause910 (q : Nat → Bool) : valuationOf q 803 = false ∨ valuationOf q 820 = false ∨ valuationOf q 831 = true := by
  have hs : count827 q = (countLit q [-1, -2, -4, -6, -7, -11, -12]) + (countLit q [-15, -16, -19, -21, -23, -26, -28]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -4, -6, -7, -11, -12]) (l₂ := [-15, -16, -19, -21, -23, -26, -28])
  have hm := merge_two (literal (valuationOf q) (803)) (literal (valuationOf q) (820)) (literal (valuationOf q) (831)) (countLit q [-1, -2, -4, -6, -7, -11, -12]) (countLit q [-15, -16, -19, -21, -23, -26, -28]) (count827 q) 4 1 (meaning803 q) (meaning820 q) (meaning831 q) hs
  change valuationOf q 803 = false ∨ valuationOf q 820 = false ∨ valuationOf q 831 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause910 (q : Snake 81) (h : Conditions q) : valuation q 803 = false ∨ valuation q 820 = false ∨ valuation q 831 = true := counterClause910 (baseVal q)

theorem counterClause911 (q : Nat → Bool) : valuationOf q 803 = false ∨ valuationOf q 821 = false ∨ valuationOf q 832 = true := by
  have hs : count827 q = (countLit q [-1, -2, -4, -6, -7, -11, -12]) + (countLit q [-15, -16, -19, -21, -23, -26, -28]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -4, -6, -7, -11, -12]) (l₂ := [-15, -16, -19, -21, -23, -26, -28])
  have hm := merge_two (literal (valuationOf q) (803)) (literal (valuationOf q) (821)) (literal (valuationOf q) (832)) (countLit q [-1, -2, -4, -6, -7, -11, -12]) (countLit q [-15, -16, -19, -21, -23, -26, -28]) (count827 q) 4 2 (meaning803 q) (meaning821 q) (meaning832 q) hs
  change valuationOf q 803 = false ∨ valuationOf q 821 = false ∨ valuationOf q 832 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause911 (q : Snake 81) (h : Conditions q) : valuation q 803 = false ∨ valuation q 821 = false ∨ valuation q 832 = true := counterClause911 (baseVal q)

theorem counterClause912 (q : Nat → Bool) : valuationOf q 803 = false ∨ valuationOf q 822 = false ∨ valuationOf q 833 = true := by
  have hs : count827 q = (countLit q [-1, -2, -4, -6, -7, -11, -12]) + (countLit q [-15, -16, -19, -21, -23, -26, -28]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -4, -6, -7, -11, -12]) (l₂ := [-15, -16, -19, -21, -23, -26, -28])
  have hm := merge_two (literal (valuationOf q) (803)) (literal (valuationOf q) (822)) (literal (valuationOf q) (833)) (countLit q [-1, -2, -4, -6, -7, -11, -12]) (countLit q [-15, -16, -19, -21, -23, -26, -28]) (count827 q) 4 3 (meaning803 q) (meaning822 q) (meaning833 q) hs
  change valuationOf q 803 = false ∨ valuationOf q 822 = false ∨ valuationOf q 833 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause912 (q : Snake 81) (h : Conditions q) : valuation q 803 = false ∨ valuation q 822 = false ∨ valuation q 833 = true := counterClause912 (baseVal q)

theorem counterClause913 (q : Nat → Bool) : valuationOf q 803 = false ∨ valuationOf q 823 = false ∨ valuationOf q 834 = true := by
  have hs : count827 q = (countLit q [-1, -2, -4, -6, -7, -11, -12]) + (countLit q [-15, -16, -19, -21, -23, -26, -28]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -4, -6, -7, -11, -12]) (l₂ := [-15, -16, -19, -21, -23, -26, -28])
  have hm := merge_two (literal (valuationOf q) (803)) (literal (valuationOf q) (823)) (literal (valuationOf q) (834)) (countLit q [-1, -2, -4, -6, -7, -11, -12]) (countLit q [-15, -16, -19, -21, -23, -26, -28]) (count827 q) 4 4 (meaning803 q) (meaning823 q) (meaning834 q) hs
  change valuationOf q 803 = false ∨ valuationOf q 823 = false ∨ valuationOf q 834 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause913 (q : Snake 81) (h : Conditions q) : valuation q 803 = false ∨ valuation q 823 = false ∨ valuation q 834 = true := counterClause913 (baseVal q)

theorem counterClause914 (q : Nat → Bool) : valuationOf q 803 = false ∨ valuationOf q 824 = false ∨ valuationOf q 835 = true := by
  have hs : count827 q = (countLit q [-1, -2, -4, -6, -7, -11, -12]) + (countLit q [-15, -16, -19, -21, -23, -26, -28]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -4, -6, -7, -11, -12]) (l₂ := [-15, -16, -19, -21, -23, -26, -28])
  have hm := merge_two (literal (valuationOf q) (803)) (literal (valuationOf q) (824)) (literal (valuationOf q) (835)) (countLit q [-1, -2, -4, -6, -7, -11, -12]) (countLit q [-15, -16, -19, -21, -23, -26, -28]) (count827 q) 4 5 (meaning803 q) (meaning824 q) (meaning835 q) hs
  change valuationOf q 803 = false ∨ valuationOf q 824 = false ∨ valuationOf q 835 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause914 (q : Snake 81) (h : Conditions q) : valuation q 803 = false ∨ valuation q 824 = false ∨ valuation q 835 = true := counterClause914 (baseVal q)

theorem counterClause915 (q : Nat → Bool) : valuationOf q 803 = false ∨ valuationOf q 825 = false ∨ valuationOf q 836 = true := by
  have hs : count827 q = (countLit q [-1, -2, -4, -6, -7, -11, -12]) + (countLit q [-15, -16, -19, -21, -23, -26, -28]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -4, -6, -7, -11, -12]) (l₂ := [-15, -16, -19, -21, -23, -26, -28])
  have hm := merge_two (literal (valuationOf q) (803)) (literal (valuationOf q) (825)) (literal (valuationOf q) (836)) (countLit q [-1, -2, -4, -6, -7, -11, -12]) (countLit q [-15, -16, -19, -21, -23, -26, -28]) (count827 q) 4 6 (meaning803 q) (meaning825 q) (meaning836 q) hs
  change valuationOf q 803 = false ∨ valuationOf q 825 = false ∨ valuationOf q 836 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause915 (q : Snake 81) (h : Conditions q) : valuation q 803 = false ∨ valuation q 825 = false ∨ valuation q 836 = true := counterClause915 (baseVal q)

theorem counterClause916 (q : Nat → Bool) : valuationOf q 804 = false ∨ valuationOf q 831 = true := by
  have hs : count827 q = (countLit q [-1, -2, -4, -6, -7, -11, -12]) + (countLit q [-15, -16, -19, -21, -23, -26, -28]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -4, -6, -7, -11, -12]) (l₂ := [-15, -16, -19, -21, -23, -26, -28])
  have hm := merge_left (literal (valuationOf q) (804)) (literal (valuationOf q) (831)) (countLit q [-1, -2, -4, -6, -7, -11, -12]) (countLit q [-15, -16, -19, -21, -23, -26, -28]) (count827 q) 5 (meaning804 q) (meaning831 q) hs
  change valuationOf q 804 = false ∨ valuationOf q 831 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause916 (q : Snake 81) (h : Conditions q) : valuation q 804 = false ∨ valuation q 831 = true := counterClause916 (baseVal q)

theorem counterClause917 (q : Nat → Bool) : valuationOf q 804 = false ∨ valuationOf q 820 = false ∨ valuationOf q 832 = true := by
  have hs : count827 q = (countLit q [-1, -2, -4, -6, -7, -11, -12]) + (countLit q [-15, -16, -19, -21, -23, -26, -28]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -4, -6, -7, -11, -12]) (l₂ := [-15, -16, -19, -21, -23, -26, -28])
  have hm := merge_two (literal (valuationOf q) (804)) (literal (valuationOf q) (820)) (literal (valuationOf q) (832)) (countLit q [-1, -2, -4, -6, -7, -11, -12]) (countLit q [-15, -16, -19, -21, -23, -26, -28]) (count827 q) 5 1 (meaning804 q) (meaning820 q) (meaning832 q) hs
  change valuationOf q 804 = false ∨ valuationOf q 820 = false ∨ valuationOf q 832 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause917 (q : Snake 81) (h : Conditions q) : valuation q 804 = false ∨ valuation q 820 = false ∨ valuation q 832 = true := counterClause917 (baseVal q)

theorem counterClause918 (q : Nat → Bool) : valuationOf q 804 = false ∨ valuationOf q 821 = false ∨ valuationOf q 833 = true := by
  have hs : count827 q = (countLit q [-1, -2, -4, -6, -7, -11, -12]) + (countLit q [-15, -16, -19, -21, -23, -26, -28]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -4, -6, -7, -11, -12]) (l₂ := [-15, -16, -19, -21, -23, -26, -28])
  have hm := merge_two (literal (valuationOf q) (804)) (literal (valuationOf q) (821)) (literal (valuationOf q) (833)) (countLit q [-1, -2, -4, -6, -7, -11, -12]) (countLit q [-15, -16, -19, -21, -23, -26, -28]) (count827 q) 5 2 (meaning804 q) (meaning821 q) (meaning833 q) hs
  change valuationOf q 804 = false ∨ valuationOf q 821 = false ∨ valuationOf q 833 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause918 (q : Snake 81) (h : Conditions q) : valuation q 804 = false ∨ valuation q 821 = false ∨ valuation q 833 = true := counterClause918 (baseVal q)

theorem counterClause919 (q : Nat → Bool) : valuationOf q 804 = false ∨ valuationOf q 822 = false ∨ valuationOf q 834 = true := by
  have hs : count827 q = (countLit q [-1, -2, -4, -6, -7, -11, -12]) + (countLit q [-15, -16, -19, -21, -23, -26, -28]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -4, -6, -7, -11, -12]) (l₂ := [-15, -16, -19, -21, -23, -26, -28])
  have hm := merge_two (literal (valuationOf q) (804)) (literal (valuationOf q) (822)) (literal (valuationOf q) (834)) (countLit q [-1, -2, -4, -6, -7, -11, -12]) (countLit q [-15, -16, -19, -21, -23, -26, -28]) (count827 q) 5 3 (meaning804 q) (meaning822 q) (meaning834 q) hs
  change valuationOf q 804 = false ∨ valuationOf q 822 = false ∨ valuationOf q 834 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause919 (q : Snake 81) (h : Conditions q) : valuation q 804 = false ∨ valuation q 822 = false ∨ valuation q 834 = true := counterClause919 (baseVal q)

theorem counterClause920 (q : Nat → Bool) : valuationOf q 804 = false ∨ valuationOf q 823 = false ∨ valuationOf q 835 = true := by
  have hs : count827 q = (countLit q [-1, -2, -4, -6, -7, -11, -12]) + (countLit q [-15, -16, -19, -21, -23, -26, -28]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -4, -6, -7, -11, -12]) (l₂ := [-15, -16, -19, -21, -23, -26, -28])
  have hm := merge_two (literal (valuationOf q) (804)) (literal (valuationOf q) (823)) (literal (valuationOf q) (835)) (countLit q [-1, -2, -4, -6, -7, -11, -12]) (countLit q [-15, -16, -19, -21, -23, -26, -28]) (count827 q) 5 4 (meaning804 q) (meaning823 q) (meaning835 q) hs
  change valuationOf q 804 = false ∨ valuationOf q 823 = false ∨ valuationOf q 835 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause920 (q : Snake 81) (h : Conditions q) : valuation q 804 = false ∨ valuation q 823 = false ∨ valuation q 835 = true := counterClause920 (baseVal q)

theorem counterClause921 (q : Nat → Bool) : valuationOf q 805 = false ∨ valuationOf q 832 = true := by
  have hs : count827 q = (countLit q [-1, -2, -4, -6, -7, -11, -12]) + (countLit q [-15, -16, -19, -21, -23, -26, -28]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -4, -6, -7, -11, -12]) (l₂ := [-15, -16, -19, -21, -23, -26, -28])
  have hm := merge_left (literal (valuationOf q) (805)) (literal (valuationOf q) (832)) (countLit q [-1, -2, -4, -6, -7, -11, -12]) (countLit q [-15, -16, -19, -21, -23, -26, -28]) (count827 q) 6 (meaning805 q) (meaning832 q) hs
  change valuationOf q 805 = false ∨ valuationOf q 832 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause921 (q : Snake 81) (h : Conditions q) : valuation q 805 = false ∨ valuation q 832 = true := counterClause921 (baseVal q)

theorem counterClause922 (q : Nat → Bool) : valuationOf q 805 = false ∨ valuationOf q 820 = false ∨ valuationOf q 833 = true := by
  have hs : count827 q = (countLit q [-1, -2, -4, -6, -7, -11, -12]) + (countLit q [-15, -16, -19, -21, -23, -26, -28]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -4, -6, -7, -11, -12]) (l₂ := [-15, -16, -19, -21, -23, -26, -28])
  have hm := merge_two (literal (valuationOf q) (805)) (literal (valuationOf q) (820)) (literal (valuationOf q) (833)) (countLit q [-1, -2, -4, -6, -7, -11, -12]) (countLit q [-15, -16, -19, -21, -23, -26, -28]) (count827 q) 6 1 (meaning805 q) (meaning820 q) (meaning833 q) hs
  change valuationOf q 805 = false ∨ valuationOf q 820 = false ∨ valuationOf q 833 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause922 (q : Snake 81) (h : Conditions q) : valuation q 805 = false ∨ valuation q 820 = false ∨ valuation q 833 = true := counterClause922 (baseVal q)

theorem counterClause923 (q : Nat → Bool) : valuationOf q 805 = false ∨ valuationOf q 821 = false ∨ valuationOf q 834 = true := by
  have hs : count827 q = (countLit q [-1, -2, -4, -6, -7, -11, -12]) + (countLit q [-15, -16, -19, -21, -23, -26, -28]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -4, -6, -7, -11, -12]) (l₂ := [-15, -16, -19, -21, -23, -26, -28])
  have hm := merge_two (literal (valuationOf q) (805)) (literal (valuationOf q) (821)) (literal (valuationOf q) (834)) (countLit q [-1, -2, -4, -6, -7, -11, -12]) (countLit q [-15, -16, -19, -21, -23, -26, -28]) (count827 q) 6 2 (meaning805 q) (meaning821 q) (meaning834 q) hs
  change valuationOf q 805 = false ∨ valuationOf q 821 = false ∨ valuationOf q 834 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause923 (q : Snake 81) (h : Conditions q) : valuation q 805 = false ∨ valuation q 821 = false ∨ valuation q 834 = true := counterClause923 (baseVal q)

theorem counterClause924 (q : Nat → Bool) : valuationOf q 34 = true ∨ valuationOf q 841 = true := by
  have hs : count841 q = (countLit q [-32]) + (countLit q [-34]) := List.countP_append (p := literal q) (l₁ := [-32]) (l₂ := [-34])
  have hm := merge_right (literal (valuationOf q) (-34)) (literal (valuationOf q) (841)) (countLit q [-32]) (countLit q [-34]) (count841 q) 1 (meaningNeg34 q) (meaning841 q) hs
  change (! (valuationOf q 34)) = false ∨ valuationOf q 841 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause924 (q : Snake 81) (h : Conditions q) : valuation q 34 = true ∨ valuation q 841 = true := counterClause924 (baseVal q)

theorem counterClause925 (q : Nat → Bool) : valuationOf q 32 = true ∨ valuationOf q 841 = true := by
  have hs : count841 q = (countLit q [-32]) + (countLit q [-34]) := List.countP_append (p := literal q) (l₁ := [-32]) (l₂ := [-34])
  have hm := merge_left (literal (valuationOf q) (-32)) (literal (valuationOf q) (841)) (countLit q [-32]) (countLit q [-34]) (count841 q) 1 (meaningNeg32 q) (meaning841 q) hs
  change (! (valuationOf q 32)) = false ∨ valuationOf q 841 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause925 (q : Snake 81) (h : Conditions q) : valuation q 32 = true ∨ valuation q 841 = true := counterClause925 (baseVal q)

theorem counterClause926 (q : Nat → Bool) : valuationOf q 32 = true ∨ valuationOf q 34 = true ∨ valuationOf q 842 = true := by
  have hs : count841 q = (countLit q [-32]) + (countLit q [-34]) := List.countP_append (p := literal q) (l₁ := [-32]) (l₂ := [-34])
  have hm := merge_two (literal (valuationOf q) (-32)) (literal (valuationOf q) (-34)) (literal (valuationOf q) (842)) (countLit q [-32]) (countLit q [-34]) (count841 q) 1 1 (meaningNeg32 q) (meaningNeg34 q) (meaning842 q) hs
  change (! (valuationOf q 32)) = false ∨ (! (valuationOf q 34)) = false ∨ valuationOf q 842 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause926 (q : Snake 81) (h : Conditions q) : valuation q 32 = true ∨ valuation q 34 = true ∨ valuation q 842 = true := counterClause926 (baseVal q)

theorem counterClause927 (q : Nat → Bool) : valuationOf q 841 = false ∨ valuationOf q 843 = true := by
  have hs : count843 q = (countLit q [-30]) + (countLit q [-32, -34]) := List.countP_append (p := literal q) (l₁ := [-30]) (l₂ := [-32, -34])
  have hm := merge_right (literal (valuationOf q) (841)) (literal (valuationOf q) (843)) (countLit q [-30]) (countLit q [-32, -34]) (count843 q) 1 (meaning841 q) (meaning843 q) hs
  change valuationOf q 841 = false ∨ valuationOf q 843 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause927 (q : Snake 81) (h : Conditions q) : valuation q 841 = false ∨ valuation q 843 = true := counterClause927 (baseVal q)

theorem counterClause928 (q : Nat → Bool) : valuationOf q 842 = false ∨ valuationOf q 844 = true := by
  have hs : count843 q = (countLit q [-30]) + (countLit q [-32, -34]) := List.countP_append (p := literal q) (l₁ := [-30]) (l₂ := [-32, -34])
  have hm := merge_right (literal (valuationOf q) (842)) (literal (valuationOf q) (844)) (countLit q [-30]) (countLit q [-32, -34]) (count843 q) 2 (meaning842 q) (meaning844 q) hs
  change valuationOf q 842 = false ∨ valuationOf q 844 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause928 (q : Snake 81) (h : Conditions q) : valuation q 842 = false ∨ valuation q 844 = true := counterClause928 (baseVal q)

theorem block28 (q : Snake 81) (h : Conditions q) : B112E257.Block28 (valuation q) :=
  ⟨clause897 q h, clause898 q h, clause899 q h, clause900 q h, clause901 q h, clause902 q h, clause903 q h, clause904 q h, clause905 q h, clause906 q h, clause907 q h, clause908 q h, clause909 q h, clause910 q h, clause911 q h, clause912 q h, clause913 q h, clause914 q h, clause915 q h, clause916 q h, clause917 q h, clause918 q h, clause919 q h, clause920 q h, clause921 q h, clause922 q h, clause923 q h, clause924 q h, clause925 q h, clause926 q h, clause927 q h, clause928 q h⟩

end
end Snake9.Regrowth.E112257
