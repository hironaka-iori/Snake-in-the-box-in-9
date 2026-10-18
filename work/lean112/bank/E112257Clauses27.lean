import E112257Semantics
import B112E257Inputs
namespace Snake9.Regrowth.E112257
noncomputable section
local instance blockDec27 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause865 (q : Nat → Bool) : valuationOf q 818 = false ∨ valuationOf q 822 = true := by
  have hs : count820 q = (countLit q [-15, -16, -19]) + (countLit q [-21, -23, -26, -28]) := List.countP_append (p := literal q) (l₁ := [-15, -16, -19]) (l₂ := [-21, -23, -26, -28])
  have hm := merge_right (literal (valuationOf q) (818)) (literal (valuationOf q) (822)) (countLit q [-15, -16, -19]) (countLit q [-21, -23, -26, -28]) (count820 q) 3 (meaning818 q) (meaning822 q) hs
  change valuationOf q 818 = false ∨ valuationOf q 822 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause865 (q : Snake 81) (h : Conditions q) : valuation q 818 = false ∨ valuation q 822 = true := counterClause865 (baseVal q)

theorem counterClause866 (q : Nat → Bool) : valuationOf q 819 = false ∨ valuationOf q 823 = true := by
  have hs : count820 q = (countLit q [-15, -16, -19]) + (countLit q [-21, -23, -26, -28]) := List.countP_append (p := literal q) (l₁ := [-15, -16, -19]) (l₂ := [-21, -23, -26, -28])
  have hm := merge_right (literal (valuationOf q) (819)) (literal (valuationOf q) (823)) (countLit q [-15, -16, -19]) (countLit q [-21, -23, -26, -28]) (count820 q) 4 (meaning819 q) (meaning823 q) hs
  change valuationOf q 819 = false ∨ valuationOf q 823 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause866 (q : Snake 81) (h : Conditions q) : valuation q 819 = false ∨ valuation q 823 = true := counterClause866 (baseVal q)

theorem counterClause867 (q : Nat → Bool) : valuationOf q 809 = false ∨ valuationOf q 820 = true := by
  have hs : count820 q = (countLit q [-15, -16, -19]) + (countLit q [-21, -23, -26, -28]) := List.countP_append (p := literal q) (l₁ := [-15, -16, -19]) (l₂ := [-21, -23, -26, -28])
  have hm := merge_left (literal (valuationOf q) (809)) (literal (valuationOf q) (820)) (countLit q [-15, -16, -19]) (countLit q [-21, -23, -26, -28]) (count820 q) 1 (meaning809 q) (meaning820 q) hs
  change valuationOf q 809 = false ∨ valuationOf q 820 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause867 (q : Snake 81) (h : Conditions q) : valuation q 809 = false ∨ valuation q 820 = true := counterClause867 (baseVal q)

theorem counterClause868 (q : Nat → Bool) : valuationOf q 809 = false ∨ valuationOf q 816 = false ∨ valuationOf q 821 = true := by
  have hs : count820 q = (countLit q [-15, -16, -19]) + (countLit q [-21, -23, -26, -28]) := List.countP_append (p := literal q) (l₁ := [-15, -16, -19]) (l₂ := [-21, -23, -26, -28])
  have hm := merge_two (literal (valuationOf q) (809)) (literal (valuationOf q) (816)) (literal (valuationOf q) (821)) (countLit q [-15, -16, -19]) (countLit q [-21, -23, -26, -28]) (count820 q) 1 1 (meaning809 q) (meaning816 q) (meaning821 q) hs
  change valuationOf q 809 = false ∨ valuationOf q 816 = false ∨ valuationOf q 821 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause868 (q : Snake 81) (h : Conditions q) : valuation q 809 = false ∨ valuation q 816 = false ∨ valuation q 821 = true := counterClause868 (baseVal q)

theorem counterClause869 (q : Nat → Bool) : valuationOf q 809 = false ∨ valuationOf q 817 = false ∨ valuationOf q 822 = true := by
  have hs : count820 q = (countLit q [-15, -16, -19]) + (countLit q [-21, -23, -26, -28]) := List.countP_append (p := literal q) (l₁ := [-15, -16, -19]) (l₂ := [-21, -23, -26, -28])
  have hm := merge_two (literal (valuationOf q) (809)) (literal (valuationOf q) (817)) (literal (valuationOf q) (822)) (countLit q [-15, -16, -19]) (countLit q [-21, -23, -26, -28]) (count820 q) 1 2 (meaning809 q) (meaning817 q) (meaning822 q) hs
  change valuationOf q 809 = false ∨ valuationOf q 817 = false ∨ valuationOf q 822 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause869 (q : Snake 81) (h : Conditions q) : valuation q 809 = false ∨ valuation q 817 = false ∨ valuation q 822 = true := counterClause869 (baseVal q)

theorem counterClause870 (q : Nat → Bool) : valuationOf q 809 = false ∨ valuationOf q 818 = false ∨ valuationOf q 823 = true := by
  have hs : count820 q = (countLit q [-15, -16, -19]) + (countLit q [-21, -23, -26, -28]) := List.countP_append (p := literal q) (l₁ := [-15, -16, -19]) (l₂ := [-21, -23, -26, -28])
  have hm := merge_two (literal (valuationOf q) (809)) (literal (valuationOf q) (818)) (literal (valuationOf q) (823)) (countLit q [-15, -16, -19]) (countLit q [-21, -23, -26, -28]) (count820 q) 1 3 (meaning809 q) (meaning818 q) (meaning823 q) hs
  change valuationOf q 809 = false ∨ valuationOf q 818 = false ∨ valuationOf q 823 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause870 (q : Snake 81) (h : Conditions q) : valuation q 809 = false ∨ valuation q 818 = false ∨ valuation q 823 = true := counterClause870 (baseVal q)

theorem counterClause871 (q : Nat → Bool) : valuationOf q 809 = false ∨ valuationOf q 819 = false ∨ valuationOf q 824 = true := by
  have hs : count820 q = (countLit q [-15, -16, -19]) + (countLit q [-21, -23, -26, -28]) := List.countP_append (p := literal q) (l₁ := [-15, -16, -19]) (l₂ := [-21, -23, -26, -28])
  have hm := merge_two (literal (valuationOf q) (809)) (literal (valuationOf q) (819)) (literal (valuationOf q) (824)) (countLit q [-15, -16, -19]) (countLit q [-21, -23, -26, -28]) (count820 q) 1 4 (meaning809 q) (meaning819 q) (meaning824 q) hs
  change valuationOf q 809 = false ∨ valuationOf q 819 = false ∨ valuationOf q 824 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause871 (q : Snake 81) (h : Conditions q) : valuation q 809 = false ∨ valuation q 819 = false ∨ valuation q 824 = true := counterClause871 (baseVal q)

theorem counterClause872 (q : Nat → Bool) : valuationOf q 810 = false ∨ valuationOf q 821 = true := by
  have hs : count820 q = (countLit q [-15, -16, -19]) + (countLit q [-21, -23, -26, -28]) := List.countP_append (p := literal q) (l₁ := [-15, -16, -19]) (l₂ := [-21, -23, -26, -28])
  have hm := merge_left (literal (valuationOf q) (810)) (literal (valuationOf q) (821)) (countLit q [-15, -16, -19]) (countLit q [-21, -23, -26, -28]) (count820 q) 2 (meaning810 q) (meaning821 q) hs
  change valuationOf q 810 = false ∨ valuationOf q 821 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause872 (q : Snake 81) (h : Conditions q) : valuation q 810 = false ∨ valuation q 821 = true := counterClause872 (baseVal q)

theorem counterClause873 (q : Nat → Bool) : valuationOf q 810 = false ∨ valuationOf q 816 = false ∨ valuationOf q 822 = true := by
  have hs : count820 q = (countLit q [-15, -16, -19]) + (countLit q [-21, -23, -26, -28]) := List.countP_append (p := literal q) (l₁ := [-15, -16, -19]) (l₂ := [-21, -23, -26, -28])
  have hm := merge_two (literal (valuationOf q) (810)) (literal (valuationOf q) (816)) (literal (valuationOf q) (822)) (countLit q [-15, -16, -19]) (countLit q [-21, -23, -26, -28]) (count820 q) 2 1 (meaning810 q) (meaning816 q) (meaning822 q) hs
  change valuationOf q 810 = false ∨ valuationOf q 816 = false ∨ valuationOf q 822 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause873 (q : Snake 81) (h : Conditions q) : valuation q 810 = false ∨ valuation q 816 = false ∨ valuation q 822 = true := counterClause873 (baseVal q)

theorem counterClause874 (q : Nat → Bool) : valuationOf q 810 = false ∨ valuationOf q 817 = false ∨ valuationOf q 823 = true := by
  have hs : count820 q = (countLit q [-15, -16, -19]) + (countLit q [-21, -23, -26, -28]) := List.countP_append (p := literal q) (l₁ := [-15, -16, -19]) (l₂ := [-21, -23, -26, -28])
  have hm := merge_two (literal (valuationOf q) (810)) (literal (valuationOf q) (817)) (literal (valuationOf q) (823)) (countLit q [-15, -16, -19]) (countLit q [-21, -23, -26, -28]) (count820 q) 2 2 (meaning810 q) (meaning817 q) (meaning823 q) hs
  change valuationOf q 810 = false ∨ valuationOf q 817 = false ∨ valuationOf q 823 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause874 (q : Snake 81) (h : Conditions q) : valuation q 810 = false ∨ valuation q 817 = false ∨ valuation q 823 = true := counterClause874 (baseVal q)

theorem counterClause875 (q : Nat → Bool) : valuationOf q 810 = false ∨ valuationOf q 818 = false ∨ valuationOf q 824 = true := by
  have hs : count820 q = (countLit q [-15, -16, -19]) + (countLit q [-21, -23, -26, -28]) := List.countP_append (p := literal q) (l₁ := [-15, -16, -19]) (l₂ := [-21, -23, -26, -28])
  have hm := merge_two (literal (valuationOf q) (810)) (literal (valuationOf q) (818)) (literal (valuationOf q) (824)) (countLit q [-15, -16, -19]) (countLit q [-21, -23, -26, -28]) (count820 q) 2 3 (meaning810 q) (meaning818 q) (meaning824 q) hs
  change valuationOf q 810 = false ∨ valuationOf q 818 = false ∨ valuationOf q 824 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause875 (q : Snake 81) (h : Conditions q) : valuation q 810 = false ∨ valuation q 818 = false ∨ valuation q 824 = true := counterClause875 (baseVal q)

theorem counterClause876 (q : Nat → Bool) : valuationOf q 810 = false ∨ valuationOf q 819 = false ∨ valuationOf q 825 = true := by
  have hs : count820 q = (countLit q [-15, -16, -19]) + (countLit q [-21, -23, -26, -28]) := List.countP_append (p := literal q) (l₁ := [-15, -16, -19]) (l₂ := [-21, -23, -26, -28])
  have hm := merge_two (literal (valuationOf q) (810)) (literal (valuationOf q) (819)) (literal (valuationOf q) (825)) (countLit q [-15, -16, -19]) (countLit q [-21, -23, -26, -28]) (count820 q) 2 4 (meaning810 q) (meaning819 q) (meaning825 q) hs
  change valuationOf q 810 = false ∨ valuationOf q 819 = false ∨ valuationOf q 825 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause876 (q : Snake 81) (h : Conditions q) : valuation q 810 = false ∨ valuation q 819 = false ∨ valuation q 825 = true := counterClause876 (baseVal q)

theorem counterClause877 (q : Nat → Bool) : valuationOf q 811 = false ∨ valuationOf q 822 = true := by
  have hs : count820 q = (countLit q [-15, -16, -19]) + (countLit q [-21, -23, -26, -28]) := List.countP_append (p := literal q) (l₁ := [-15, -16, -19]) (l₂ := [-21, -23, -26, -28])
  have hm := merge_left (literal (valuationOf q) (811)) (literal (valuationOf q) (822)) (countLit q [-15, -16, -19]) (countLit q [-21, -23, -26, -28]) (count820 q) 3 (meaning811 q) (meaning822 q) hs
  change valuationOf q 811 = false ∨ valuationOf q 822 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause877 (q : Snake 81) (h : Conditions q) : valuation q 811 = false ∨ valuation q 822 = true := counterClause877 (baseVal q)

theorem counterClause878 (q : Nat → Bool) : valuationOf q 811 = false ∨ valuationOf q 816 = false ∨ valuationOf q 823 = true := by
  have hs : count820 q = (countLit q [-15, -16, -19]) + (countLit q [-21, -23, -26, -28]) := List.countP_append (p := literal q) (l₁ := [-15, -16, -19]) (l₂ := [-21, -23, -26, -28])
  have hm := merge_two (literal (valuationOf q) (811)) (literal (valuationOf q) (816)) (literal (valuationOf q) (823)) (countLit q [-15, -16, -19]) (countLit q [-21, -23, -26, -28]) (count820 q) 3 1 (meaning811 q) (meaning816 q) (meaning823 q) hs
  change valuationOf q 811 = false ∨ valuationOf q 816 = false ∨ valuationOf q 823 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause878 (q : Snake 81) (h : Conditions q) : valuation q 811 = false ∨ valuation q 816 = false ∨ valuation q 823 = true := counterClause878 (baseVal q)

theorem counterClause879 (q : Nat → Bool) : valuationOf q 811 = false ∨ valuationOf q 817 = false ∨ valuationOf q 824 = true := by
  have hs : count820 q = (countLit q [-15, -16, -19]) + (countLit q [-21, -23, -26, -28]) := List.countP_append (p := literal q) (l₁ := [-15, -16, -19]) (l₂ := [-21, -23, -26, -28])
  have hm := merge_two (literal (valuationOf q) (811)) (literal (valuationOf q) (817)) (literal (valuationOf q) (824)) (countLit q [-15, -16, -19]) (countLit q [-21, -23, -26, -28]) (count820 q) 3 2 (meaning811 q) (meaning817 q) (meaning824 q) hs
  change valuationOf q 811 = false ∨ valuationOf q 817 = false ∨ valuationOf q 824 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause879 (q : Snake 81) (h : Conditions q) : valuation q 811 = false ∨ valuation q 817 = false ∨ valuation q 824 = true := counterClause879 (baseVal q)

theorem counterClause880 (q : Nat → Bool) : valuationOf q 811 = false ∨ valuationOf q 818 = false ∨ valuationOf q 825 = true := by
  have hs : count820 q = (countLit q [-15, -16, -19]) + (countLit q [-21, -23, -26, -28]) := List.countP_append (p := literal q) (l₁ := [-15, -16, -19]) (l₂ := [-21, -23, -26, -28])
  have hm := merge_two (literal (valuationOf q) (811)) (literal (valuationOf q) (818)) (literal (valuationOf q) (825)) (countLit q [-15, -16, -19]) (countLit q [-21, -23, -26, -28]) (count820 q) 3 3 (meaning811 q) (meaning818 q) (meaning825 q) hs
  change valuationOf q 811 = false ∨ valuationOf q 818 = false ∨ valuationOf q 825 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause880 (q : Snake 81) (h : Conditions q) : valuation q 811 = false ∨ valuation q 818 = false ∨ valuation q 825 = true := counterClause880 (baseVal q)

theorem counterClause881 (q : Nat → Bool) : valuationOf q 811 = false ∨ valuationOf q 819 = false ∨ valuationOf q 826 = true := by
  have hs : count820 q = (countLit q [-15, -16, -19]) + (countLit q [-21, -23, -26, -28]) := List.countP_append (p := literal q) (l₁ := [-15, -16, -19]) (l₂ := [-21, -23, -26, -28])
  have hm := merge_two (literal (valuationOf q) (811)) (literal (valuationOf q) (819)) (literal (valuationOf q) (826)) (countLit q [-15, -16, -19]) (countLit q [-21, -23, -26, -28]) (count820 q) 3 4 (meaning811 q) (meaning819 q) (meaning826 q) hs
  change valuationOf q 811 = false ∨ valuationOf q 819 = false ∨ valuationOf q 826 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause881 (q : Snake 81) (h : Conditions q) : valuation q 811 = false ∨ valuation q 819 = false ∨ valuation q 826 = true := counterClause881 (baseVal q)

theorem counterClause882 (q : Nat → Bool) : valuationOf q 821 = false ∨ valuationOf q 828 = true := by
  have hs : count827 q = (countLit q [-1, -2, -4, -6, -7, -11, -12]) + (countLit q [-15, -16, -19, -21, -23, -26, -28]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -4, -6, -7, -11, -12]) (l₂ := [-15, -16, -19, -21, -23, -26, -28])
  have hm := merge_right (literal (valuationOf q) (821)) (literal (valuationOf q) (828)) (countLit q [-1, -2, -4, -6, -7, -11, -12]) (countLit q [-15, -16, -19, -21, -23, -26, -28]) (count827 q) 2 (meaning821 q) (meaning828 q) hs
  change valuationOf q 821 = false ∨ valuationOf q 828 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause882 (q : Snake 81) (h : Conditions q) : valuation q 821 = false ∨ valuation q 828 = true := counterClause882 (baseVal q)

theorem counterClause883 (q : Nat → Bool) : valuationOf q 822 = false ∨ valuationOf q 829 = true := by
  have hs : count827 q = (countLit q [-1, -2, -4, -6, -7, -11, -12]) + (countLit q [-15, -16, -19, -21, -23, -26, -28]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -4, -6, -7, -11, -12]) (l₂ := [-15, -16, -19, -21, -23, -26, -28])
  have hm := merge_right (literal (valuationOf q) (822)) (literal (valuationOf q) (829)) (countLit q [-1, -2, -4, -6, -7, -11, -12]) (countLit q [-15, -16, -19, -21, -23, -26, -28]) (count827 q) 3 (meaning822 q) (meaning829 q) hs
  change valuationOf q 822 = false ∨ valuationOf q 829 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause883 (q : Snake 81) (h : Conditions q) : valuation q 822 = false ∨ valuation q 829 = true := counterClause883 (baseVal q)

theorem counterClause884 (q : Nat → Bool) : valuationOf q 823 = false ∨ valuationOf q 830 = true := by
  have hs : count827 q = (countLit q [-1, -2, -4, -6, -7, -11, -12]) + (countLit q [-15, -16, -19, -21, -23, -26, -28]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -4, -6, -7, -11, -12]) (l₂ := [-15, -16, -19, -21, -23, -26, -28])
  have hm := merge_right (literal (valuationOf q) (823)) (literal (valuationOf q) (830)) (countLit q [-1, -2, -4, -6, -7, -11, -12]) (countLit q [-15, -16, -19, -21, -23, -26, -28]) (count827 q) 4 (meaning823 q) (meaning830 q) hs
  change valuationOf q 823 = false ∨ valuationOf q 830 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause884 (q : Snake 81) (h : Conditions q) : valuation q 823 = false ∨ valuation q 830 = true := counterClause884 (baseVal q)

theorem counterClause885 (q : Nat → Bool) : valuationOf q 824 = false ∨ valuationOf q 831 = true := by
  have hs : count827 q = (countLit q [-1, -2, -4, -6, -7, -11, -12]) + (countLit q [-15, -16, -19, -21, -23, -26, -28]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -4, -6, -7, -11, -12]) (l₂ := [-15, -16, -19, -21, -23, -26, -28])
  have hm := merge_right (literal (valuationOf q) (824)) (literal (valuationOf q) (831)) (countLit q [-1, -2, -4, -6, -7, -11, -12]) (countLit q [-15, -16, -19, -21, -23, -26, -28]) (count827 q) 5 (meaning824 q) (meaning831 q) hs
  change valuationOf q 824 = false ∨ valuationOf q 831 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause885 (q : Snake 81) (h : Conditions q) : valuation q 824 = false ∨ valuation q 831 = true := counterClause885 (baseVal q)

theorem counterClause886 (q : Nat → Bool) : valuationOf q 800 = false ∨ valuationOf q 827 = true := by
  have hs : count827 q = (countLit q [-1, -2, -4, -6, -7, -11, -12]) + (countLit q [-15, -16, -19, -21, -23, -26, -28]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -4, -6, -7, -11, -12]) (l₂ := [-15, -16, -19, -21, -23, -26, -28])
  have hm := merge_left (literal (valuationOf q) (800)) (literal (valuationOf q) (827)) (countLit q [-1, -2, -4, -6, -7, -11, -12]) (countLit q [-15, -16, -19, -21, -23, -26, -28]) (count827 q) 1 (meaning800 q) (meaning827 q) hs
  change valuationOf q 800 = false ∨ valuationOf q 827 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause886 (q : Snake 81) (h : Conditions q) : valuation q 800 = false ∨ valuation q 827 = true := counterClause886 (baseVal q)

theorem counterClause887 (q : Nat → Bool) : valuationOf q 800 = false ∨ valuationOf q 820 = false ∨ valuationOf q 828 = true := by
  have hs : count827 q = (countLit q [-1, -2, -4, -6, -7, -11, -12]) + (countLit q [-15, -16, -19, -21, -23, -26, -28]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -4, -6, -7, -11, -12]) (l₂ := [-15, -16, -19, -21, -23, -26, -28])
  have hm := merge_two (literal (valuationOf q) (800)) (literal (valuationOf q) (820)) (literal (valuationOf q) (828)) (countLit q [-1, -2, -4, -6, -7, -11, -12]) (countLit q [-15, -16, -19, -21, -23, -26, -28]) (count827 q) 1 1 (meaning800 q) (meaning820 q) (meaning828 q) hs
  change valuationOf q 800 = false ∨ valuationOf q 820 = false ∨ valuationOf q 828 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause887 (q : Snake 81) (h : Conditions q) : valuation q 800 = false ∨ valuation q 820 = false ∨ valuation q 828 = true := counterClause887 (baseVal q)

theorem counterClause888 (q : Nat → Bool) : valuationOf q 800 = false ∨ valuationOf q 821 = false ∨ valuationOf q 829 = true := by
  have hs : count827 q = (countLit q [-1, -2, -4, -6, -7, -11, -12]) + (countLit q [-15, -16, -19, -21, -23, -26, -28]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -4, -6, -7, -11, -12]) (l₂ := [-15, -16, -19, -21, -23, -26, -28])
  have hm := merge_two (literal (valuationOf q) (800)) (literal (valuationOf q) (821)) (literal (valuationOf q) (829)) (countLit q [-1, -2, -4, -6, -7, -11, -12]) (countLit q [-15, -16, -19, -21, -23, -26, -28]) (count827 q) 1 2 (meaning800 q) (meaning821 q) (meaning829 q) hs
  change valuationOf q 800 = false ∨ valuationOf q 821 = false ∨ valuationOf q 829 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause888 (q : Snake 81) (h : Conditions q) : valuation q 800 = false ∨ valuation q 821 = false ∨ valuation q 829 = true := counterClause888 (baseVal q)

theorem counterClause889 (q : Nat → Bool) : valuationOf q 800 = false ∨ valuationOf q 822 = false ∨ valuationOf q 830 = true := by
  have hs : count827 q = (countLit q [-1, -2, -4, -6, -7, -11, -12]) + (countLit q [-15, -16, -19, -21, -23, -26, -28]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -4, -6, -7, -11, -12]) (l₂ := [-15, -16, -19, -21, -23, -26, -28])
  have hm := merge_two (literal (valuationOf q) (800)) (literal (valuationOf q) (822)) (literal (valuationOf q) (830)) (countLit q [-1, -2, -4, -6, -7, -11, -12]) (countLit q [-15, -16, -19, -21, -23, -26, -28]) (count827 q) 1 3 (meaning800 q) (meaning822 q) (meaning830 q) hs
  change valuationOf q 800 = false ∨ valuationOf q 822 = false ∨ valuationOf q 830 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause889 (q : Snake 81) (h : Conditions q) : valuation q 800 = false ∨ valuation q 822 = false ∨ valuation q 830 = true := counterClause889 (baseVal q)

theorem counterClause890 (q : Nat → Bool) : valuationOf q 800 = false ∨ valuationOf q 823 = false ∨ valuationOf q 831 = true := by
  have hs : count827 q = (countLit q [-1, -2, -4, -6, -7, -11, -12]) + (countLit q [-15, -16, -19, -21, -23, -26, -28]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -4, -6, -7, -11, -12]) (l₂ := [-15, -16, -19, -21, -23, -26, -28])
  have hm := merge_two (literal (valuationOf q) (800)) (literal (valuationOf q) (823)) (literal (valuationOf q) (831)) (countLit q [-1, -2, -4, -6, -7, -11, -12]) (countLit q [-15, -16, -19, -21, -23, -26, -28]) (count827 q) 1 4 (meaning800 q) (meaning823 q) (meaning831 q) hs
  change valuationOf q 800 = false ∨ valuationOf q 823 = false ∨ valuationOf q 831 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause890 (q : Snake 81) (h : Conditions q) : valuation q 800 = false ∨ valuation q 823 = false ∨ valuation q 831 = true := counterClause890 (baseVal q)

theorem counterClause891 (q : Nat → Bool) : valuationOf q 800 = false ∨ valuationOf q 824 = false ∨ valuationOf q 832 = true := by
  have hs : count827 q = (countLit q [-1, -2, -4, -6, -7, -11, -12]) + (countLit q [-15, -16, -19, -21, -23, -26, -28]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -4, -6, -7, -11, -12]) (l₂ := [-15, -16, -19, -21, -23, -26, -28])
  have hm := merge_two (literal (valuationOf q) (800)) (literal (valuationOf q) (824)) (literal (valuationOf q) (832)) (countLit q [-1, -2, -4, -6, -7, -11, -12]) (countLit q [-15, -16, -19, -21, -23, -26, -28]) (count827 q) 1 5 (meaning800 q) (meaning824 q) (meaning832 q) hs
  change valuationOf q 800 = false ∨ valuationOf q 824 = false ∨ valuationOf q 832 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause891 (q : Snake 81) (h : Conditions q) : valuation q 800 = false ∨ valuation q 824 = false ∨ valuation q 832 = true := counterClause891 (baseVal q)

theorem counterClause892 (q : Nat → Bool) : valuationOf q 800 = false ∨ valuationOf q 825 = false ∨ valuationOf q 833 = true := by
  have hs : count827 q = (countLit q [-1, -2, -4, -6, -7, -11, -12]) + (countLit q [-15, -16, -19, -21, -23, -26, -28]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -4, -6, -7, -11, -12]) (l₂ := [-15, -16, -19, -21, -23, -26, -28])
  have hm := merge_two (literal (valuationOf q) (800)) (literal (valuationOf q) (825)) (literal (valuationOf q) (833)) (countLit q [-1, -2, -4, -6, -7, -11, -12]) (countLit q [-15, -16, -19, -21, -23, -26, -28]) (count827 q) 1 6 (meaning800 q) (meaning825 q) (meaning833 q) hs
  change valuationOf q 800 = false ∨ valuationOf q 825 = false ∨ valuationOf q 833 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause892 (q : Snake 81) (h : Conditions q) : valuation q 800 = false ∨ valuation q 825 = false ∨ valuation q 833 = true := counterClause892 (baseVal q)

theorem counterClause893 (q : Nat → Bool) : valuationOf q 800 = false ∨ valuationOf q 826 = false ∨ valuationOf q 834 = true := by
  have hs : count827 q = (countLit q [-1, -2, -4, -6, -7, -11, -12]) + (countLit q [-15, -16, -19, -21, -23, -26, -28]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -4, -6, -7, -11, -12]) (l₂ := [-15, -16, -19, -21, -23, -26, -28])
  have hm := merge_two (literal (valuationOf q) (800)) (literal (valuationOf q) (826)) (literal (valuationOf q) (834)) (countLit q [-1, -2, -4, -6, -7, -11, -12]) (countLit q [-15, -16, -19, -21, -23, -26, -28]) (count827 q) 1 7 (meaning800 q) (meaning826 q) (meaning834 q) hs
  change valuationOf q 800 = false ∨ valuationOf q 826 = false ∨ valuationOf q 834 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause893 (q : Snake 81) (h : Conditions q) : valuation q 800 = false ∨ valuation q 826 = false ∨ valuation q 834 = true := counterClause893 (baseVal q)

theorem counterClause894 (q : Nat → Bool) : valuationOf q 801 = false ∨ valuationOf q 828 = true := by
  have hs : count827 q = (countLit q [-1, -2, -4, -6, -7, -11, -12]) + (countLit q [-15, -16, -19, -21, -23, -26, -28]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -4, -6, -7, -11, -12]) (l₂ := [-15, -16, -19, -21, -23, -26, -28])
  have hm := merge_left (literal (valuationOf q) (801)) (literal (valuationOf q) (828)) (countLit q [-1, -2, -4, -6, -7, -11, -12]) (countLit q [-15, -16, -19, -21, -23, -26, -28]) (count827 q) 2 (meaning801 q) (meaning828 q) hs
  change valuationOf q 801 = false ∨ valuationOf q 828 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause894 (q : Snake 81) (h : Conditions q) : valuation q 801 = false ∨ valuation q 828 = true := counterClause894 (baseVal q)

theorem counterClause895 (q : Nat → Bool) : valuationOf q 801 = false ∨ valuationOf q 820 = false ∨ valuationOf q 829 = true := by
  have hs : count827 q = (countLit q [-1, -2, -4, -6, -7, -11, -12]) + (countLit q [-15, -16, -19, -21, -23, -26, -28]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -4, -6, -7, -11, -12]) (l₂ := [-15, -16, -19, -21, -23, -26, -28])
  have hm := merge_two (literal (valuationOf q) (801)) (literal (valuationOf q) (820)) (literal (valuationOf q) (829)) (countLit q [-1, -2, -4, -6, -7, -11, -12]) (countLit q [-15, -16, -19, -21, -23, -26, -28]) (count827 q) 2 1 (meaning801 q) (meaning820 q) (meaning829 q) hs
  change valuationOf q 801 = false ∨ valuationOf q 820 = false ∨ valuationOf q 829 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause895 (q : Snake 81) (h : Conditions q) : valuation q 801 = false ∨ valuation q 820 = false ∨ valuation q 829 = true := counterClause895 (baseVal q)

theorem counterClause896 (q : Nat → Bool) : valuationOf q 801 = false ∨ valuationOf q 821 = false ∨ valuationOf q 830 = true := by
  have hs : count827 q = (countLit q [-1, -2, -4, -6, -7, -11, -12]) + (countLit q [-15, -16, -19, -21, -23, -26, -28]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -4, -6, -7, -11, -12]) (l₂ := [-15, -16, -19, -21, -23, -26, -28])
  have hm := merge_two (literal (valuationOf q) (801)) (literal (valuationOf q) (821)) (literal (valuationOf q) (830)) (countLit q [-1, -2, -4, -6, -7, -11, -12]) (countLit q [-15, -16, -19, -21, -23, -26, -28]) (count827 q) 2 2 (meaning801 q) (meaning821 q) (meaning830 q) hs
  change valuationOf q 801 = false ∨ valuationOf q 821 = false ∨ valuationOf q 830 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause896 (q : Snake 81) (h : Conditions q) : valuation q 801 = false ∨ valuation q 821 = false ∨ valuation q 830 = true := counterClause896 (baseVal q)

theorem block27 (q : Snake 81) (h : Conditions q) : B112E257.Block27 (valuation q) :=
  ⟨clause865 q h, clause866 q h, clause867 q h, clause868 q h, clause869 q h, clause870 q h, clause871 q h, clause872 q h, clause873 q h, clause874 q h, clause875 q h, clause876 q h, clause877 q h, clause878 q h, clause879 q h, clause880 q h, clause881 q h, clause882 q h, clause883 q h, clause884 q h, clause885 q h, clause886 q h, clause887 q h, clause888 q h, clause889 q h, clause890 q h, clause891 q h, clause892 q h, clause893 q h, clause894 q h, clause895 q h, clause896 q h⟩

end
end Snake9.Regrowth.E112257
