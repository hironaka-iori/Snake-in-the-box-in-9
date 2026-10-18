import E112051Semantics
import B112E051Inputs
namespace Snake9.Regrowth.E112051
noncomputable section
local instance blockDec19 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause609 (q : Nat → Bool) : valuationOf q 849 = false ∨ valuationOf q 870 = false ∨ valuationOf q 879 = true := by
  have hs : count875 q = (countLit q [-31, -32, -34, -37, -38, -40, -41]) + (countLit q [-42, -47, -48, -49, -51, -54, -55]) := List.countP_append (p := literal q) (l₁ := [-31, -32, -34, -37, -38, -40, -41]) (l₂ := [-42, -47, -48, -49, -51, -54, -55])
  have hm := merge_two (literal (valuationOf q) (849)) (literal (valuationOf q) (870)) (literal (valuationOf q) (879)) (countLit q [-31, -32, -34, -37, -38, -40, -41]) (countLit q [-42, -47, -48, -49, -51, -54, -55]) (count875 q) 2 3 (meaning849 q) (meaning870 q) (meaning879 q) hs
  change valuationOf q 849 = false ∨ valuationOf q 870 = false ∨ valuationOf q 879 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause609 (q : Snake 81) (h : Conditions q) : valuation q 849 = false ∨ valuation q 870 = false ∨ valuation q 879 = true := counterClause609 (baseVal q)

theorem counterClause610 (q : Nat → Bool) : valuationOf q 850 = false ∨ valuationOf q 868 = false ∨ valuationOf q 878 = true := by
  have hs : count875 q = (countLit q [-31, -32, -34, -37, -38, -40, -41]) + (countLit q [-42, -47, -48, -49, -51, -54, -55]) := List.countP_append (p := literal q) (l₁ := [-31, -32, -34, -37, -38, -40, -41]) (l₂ := [-42, -47, -48, -49, -51, -54, -55])
  have hm := merge_two (literal (valuationOf q) (850)) (literal (valuationOf q) (868)) (literal (valuationOf q) (878)) (countLit q [-31, -32, -34, -37, -38, -40, -41]) (countLit q [-42, -47, -48, -49, -51, -54, -55]) (count875 q) 3 1 (meaning850 q) (meaning868 q) (meaning878 q) hs
  change valuationOf q 850 = false ∨ valuationOf q 868 = false ∨ valuationOf q 878 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause610 (q : Snake 81) (h : Conditions q) : valuation q 850 = false ∨ valuation q 868 = false ∨ valuation q 878 = true := counterClause610 (baseVal q)

theorem counterClause611 (q : Nat → Bool) : valuationOf q 850 = false ∨ valuationOf q 869 = false ∨ valuationOf q 879 = true := by
  have hs : count875 q = (countLit q [-31, -32, -34, -37, -38, -40, -41]) + (countLit q [-42, -47, -48, -49, -51, -54, -55]) := List.countP_append (p := literal q) (l₁ := [-31, -32, -34, -37, -38, -40, -41]) (l₂ := [-42, -47, -48, -49, -51, -54, -55])
  have hm := merge_two (literal (valuationOf q) (850)) (literal (valuationOf q) (869)) (literal (valuationOf q) (879)) (countLit q [-31, -32, -34, -37, -38, -40, -41]) (countLit q [-42, -47, -48, -49, -51, -54, -55]) (count875 q) 3 2 (meaning850 q) (meaning869 q) (meaning879 q) hs
  change valuationOf q 850 = false ∨ valuationOf q 869 = false ∨ valuationOf q 879 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause611 (q : Snake 81) (h : Conditions q) : valuation q 850 = false ∨ valuation q 869 = false ∨ valuation q 879 = true := counterClause611 (baseVal q)

theorem counterClause612 (q : Nat → Bool) : valuationOf q 850 = false ∨ valuationOf q 871 = false ∨ valuationOf q 881 = true := by
  have hs : count875 q = (countLit q [-31, -32, -34, -37, -38, -40, -41]) + (countLit q [-42, -47, -48, -49, -51, -54, -55]) := List.countP_append (p := literal q) (l₁ := [-31, -32, -34, -37, -38, -40, -41]) (l₂ := [-42, -47, -48, -49, -51, -54, -55])
  have hm := merge_two (literal (valuationOf q) (850)) (literal (valuationOf q) (871)) (literal (valuationOf q) (881)) (countLit q [-31, -32, -34, -37, -38, -40, -41]) (countLit q [-42, -47, -48, -49, -51, -54, -55]) (count875 q) 3 4 (meaning850 q) (meaning871 q) (meaning881 q) hs
  change valuationOf q 850 = false ∨ valuationOf q 871 = false ∨ valuationOf q 881 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause612 (q : Snake 81) (h : Conditions q) : valuation q 850 = false ∨ valuation q 871 = false ∨ valuation q 881 = true := counterClause612 (baseVal q)

theorem counterClause613 (q : Nat → Bool) : valuationOf q 851 = false ∨ valuationOf q 868 = false ∨ valuationOf q 879 = true := by
  have hs : count875 q = (countLit q [-31, -32, -34, -37, -38, -40, -41]) + (countLit q [-42, -47, -48, -49, -51, -54, -55]) := List.countP_append (p := literal q) (l₁ := [-31, -32, -34, -37, -38, -40, -41]) (l₂ := [-42, -47, -48, -49, -51, -54, -55])
  have hm := merge_two (literal (valuationOf q) (851)) (literal (valuationOf q) (868)) (literal (valuationOf q) (879)) (countLit q [-31, -32, -34, -37, -38, -40, -41]) (countLit q [-42, -47, -48, -49, -51, -54, -55]) (count875 q) 4 1 (meaning851 q) (meaning868 q) (meaning879 q) hs
  change valuationOf q 851 = false ∨ valuationOf q 868 = false ∨ valuationOf q 879 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause613 (q : Snake 81) (h : Conditions q) : valuation q 851 = false ∨ valuation q 868 = false ∨ valuation q 879 = true := counterClause613 (baseVal q)

theorem counterClause614 (q : Nat → Bool) : valuationOf q 851 = false ∨ valuationOf q 870 = false ∨ valuationOf q 881 = true := by
  have hs : count875 q = (countLit q [-31, -32, -34, -37, -38, -40, -41]) + (countLit q [-42, -47, -48, -49, -51, -54, -55]) := List.countP_append (p := literal q) (l₁ := [-31, -32, -34, -37, -38, -40, -41]) (l₂ := [-42, -47, -48, -49, -51, -54, -55])
  have hm := merge_two (literal (valuationOf q) (851)) (literal (valuationOf q) (870)) (literal (valuationOf q) (881)) (countLit q [-31, -32, -34, -37, -38, -40, -41]) (countLit q [-42, -47, -48, -49, -51, -54, -55]) (count875 q) 4 3 (meaning851 q) (meaning870 q) (meaning881 q) hs
  change valuationOf q 851 = false ∨ valuationOf q 870 = false ∨ valuationOf q 881 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause614 (q : Snake 81) (h : Conditions q) : valuation q 851 = false ∨ valuation q 870 = false ∨ valuation q 881 = true := counterClause614 (baseVal q)

theorem counterClause615 (q : Nat → Bool) : valuationOf q 822 = false ∨ valuationOf q 878 = false ∨ valuationOf q 894 = true := by
  have hs : count889 q = (countLit q [-1, -3, -6, -8, -9, -10, -15, -16, -17, -20, -24, -26, -27, -30]) + (countLit q [-31, -32, -34, -37, -38, -40, -41, -42, -47, -48, -49, -51, -54, -55]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -6, -8, -9, -10, -15, -16, -17, -20, -24, -26, -27, -30]) (l₂ := [-31, -32, -34, -37, -38, -40, -41, -42, -47, -48, -49, -51, -54, -55])
  have hm := merge_two (literal (valuationOf q) (822)) (literal (valuationOf q) (878)) (literal (valuationOf q) (894)) (countLit q [-1, -3, -6, -8, -9, -10, -15, -16, -17, -20, -24, -26, -27, -30]) (countLit q [-31, -32, -34, -37, -38, -40, -41, -42, -47, -48, -49, -51, -54, -55]) (count889 q) 2 4 (meaning822 q) (meaning878 q) (meaning894 q) hs
  change valuationOf q 822 = false ∨ valuationOf q 878 = false ∨ valuationOf q 894 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause615 (q : Snake 81) (h : Conditions q) : valuation q 822 = false ∨ valuation q 878 = false ∨ valuation q 894 = true := counterClause615 (baseVal q)

theorem counterClause616 (q : Nat → Bool) : valuationOf q 822 = false ∨ valuationOf q 879 = false ∨ valuationOf q 895 = true := by
  have hs : count889 q = (countLit q [-1, -3, -6, -8, -9, -10, -15, -16, -17, -20, -24, -26, -27, -30]) + (countLit q [-31, -32, -34, -37, -38, -40, -41, -42, -47, -48, -49, -51, -54, -55]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -6, -8, -9, -10, -15, -16, -17, -20, -24, -26, -27, -30]) (l₂ := [-31, -32, -34, -37, -38, -40, -41, -42, -47, -48, -49, -51, -54, -55])
  have hm := merge_two (literal (valuationOf q) (822)) (literal (valuationOf q) (879)) (literal (valuationOf q) (895)) (countLit q [-1, -3, -6, -8, -9, -10, -15, -16, -17, -20, -24, -26, -27, -30]) (countLit q [-31, -32, -34, -37, -38, -40, -41, -42, -47, -48, -49, -51, -54, -55]) (count889 q) 2 5 (meaning822 q) (meaning879 q) (meaning895 q) hs
  change valuationOf q 822 = false ∨ valuationOf q 879 = false ∨ valuationOf q 895 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause616 (q : Snake 81) (h : Conditions q) : valuation q 822 = false ∨ valuation q 879 = false ∨ valuation q 895 = true := counterClause616 (baseVal q)

theorem counterClause617 (q : Nat → Bool) : valuationOf q 822 = false ∨ valuationOf q 881 = false ∨ valuationOf q 897 = true := by
  have hs : count889 q = (countLit q [-1, -3, -6, -8, -9, -10, -15, -16, -17, -20, -24, -26, -27, -30]) + (countLit q [-31, -32, -34, -37, -38, -40, -41, -42, -47, -48, -49, -51, -54, -55]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -6, -8, -9, -10, -15, -16, -17, -20, -24, -26, -27, -30]) (l₂ := [-31, -32, -34, -37, -38, -40, -41, -42, -47, -48, -49, -51, -54, -55])
  have hm := merge_two (literal (valuationOf q) (822)) (literal (valuationOf q) (881)) (literal (valuationOf q) (897)) (countLit q [-1, -3, -6, -8, -9, -10, -15, -16, -17, -20, -24, -26, -27, -30]) (countLit q [-31, -32, -34, -37, -38, -40, -41, -42, -47, -48, -49, -51, -54, -55]) (count889 q) 2 7 (meaning822 q) (meaning881 q) (meaning897 q) hs
  change valuationOf q 822 = false ∨ valuationOf q 881 = false ∨ valuationOf q 897 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause617 (q : Snake 81) (h : Conditions q) : valuation q 822 = false ∨ valuation q 881 = false ∨ valuation q 897 = true := counterClause617 (baseVal q)

theorem counterClause618 (q : Nat → Bool) : valuationOf q 823 = false ∨ valuationOf q 877 = false ∨ valuationOf q 894 = true := by
  have hs : count889 q = (countLit q [-1, -3, -6, -8, -9, -10, -15, -16, -17, -20, -24, -26, -27, -30]) + (countLit q [-31, -32, -34, -37, -38, -40, -41, -42, -47, -48, -49, -51, -54, -55]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -6, -8, -9, -10, -15, -16, -17, -20, -24, -26, -27, -30]) (l₂ := [-31, -32, -34, -37, -38, -40, -41, -42, -47, -48, -49, -51, -54, -55])
  have hm := merge_two (literal (valuationOf q) (823)) (literal (valuationOf q) (877)) (literal (valuationOf q) (894)) (countLit q [-1, -3, -6, -8, -9, -10, -15, -16, -17, -20, -24, -26, -27, -30]) (countLit q [-31, -32, -34, -37, -38, -40, -41, -42, -47, -48, -49, -51, -54, -55]) (count889 q) 3 3 (meaning823 q) (meaning877 q) (meaning894 q) hs
  change valuationOf q 823 = false ∨ valuationOf q 877 = false ∨ valuationOf q 894 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause618 (q : Snake 81) (h : Conditions q) : valuation q 823 = false ∨ valuation q 877 = false ∨ valuation q 894 = true := counterClause618 (baseVal q)

theorem counterClause619 (q : Nat → Bool) : valuationOf q 823 = false ∨ valuationOf q 878 = false ∨ valuationOf q 895 = true := by
  have hs : count889 q = (countLit q [-1, -3, -6, -8, -9, -10, -15, -16, -17, -20, -24, -26, -27, -30]) + (countLit q [-31, -32, -34, -37, -38, -40, -41, -42, -47, -48, -49, -51, -54, -55]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -6, -8, -9, -10, -15, -16, -17, -20, -24, -26, -27, -30]) (l₂ := [-31, -32, -34, -37, -38, -40, -41, -42, -47, -48, -49, -51, -54, -55])
  have hm := merge_two (literal (valuationOf q) (823)) (literal (valuationOf q) (878)) (literal (valuationOf q) (895)) (countLit q [-1, -3, -6, -8, -9, -10, -15, -16, -17, -20, -24, -26, -27, -30]) (countLit q [-31, -32, -34, -37, -38, -40, -41, -42, -47, -48, -49, -51, -54, -55]) (count889 q) 3 4 (meaning823 q) (meaning878 q) (meaning895 q) hs
  change valuationOf q 823 = false ∨ valuationOf q 878 = false ∨ valuationOf q 895 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause619 (q : Snake 81) (h : Conditions q) : valuation q 823 = false ∨ valuation q 878 = false ∨ valuation q 895 = true := counterClause619 (baseVal q)

theorem counterClause620 (q : Nat → Bool) : valuationOf q 824 = false ∨ valuationOf q 876 = false ∨ valuationOf q 894 = true := by
  have hs : count889 q = (countLit q [-1, -3, -6, -8, -9, -10, -15, -16, -17, -20, -24, -26, -27, -30]) + (countLit q [-31, -32, -34, -37, -38, -40, -41, -42, -47, -48, -49, -51, -54, -55]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -6, -8, -9, -10, -15, -16, -17, -20, -24, -26, -27, -30]) (l₂ := [-31, -32, -34, -37, -38, -40, -41, -42, -47, -48, -49, -51, -54, -55])
  have hm := merge_two (literal (valuationOf q) (824)) (literal (valuationOf q) (876)) (literal (valuationOf q) (894)) (countLit q [-1, -3, -6, -8, -9, -10, -15, -16, -17, -20, -24, -26, -27, -30]) (countLit q [-31, -32, -34, -37, -38, -40, -41, -42, -47, -48, -49, -51, -54, -55]) (count889 q) 4 2 (meaning824 q) (meaning876 q) (meaning894 q) hs
  change valuationOf q 824 = false ∨ valuationOf q 876 = false ∨ valuationOf q 894 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause620 (q : Snake 81) (h : Conditions q) : valuation q 824 = false ∨ valuation q 876 = false ∨ valuation q 894 = true := counterClause620 (baseVal q)

theorem counterClause621 (q : Nat → Bool) : valuationOf q 824 = false ∨ valuationOf q 877 = false ∨ valuationOf q 895 = true := by
  have hs : count889 q = (countLit q [-1, -3, -6, -8, -9, -10, -15, -16, -17, -20, -24, -26, -27, -30]) + (countLit q [-31, -32, -34, -37, -38, -40, -41, -42, -47, -48, -49, -51, -54, -55]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -6, -8, -9, -10, -15, -16, -17, -20, -24, -26, -27, -30]) (l₂ := [-31, -32, -34, -37, -38, -40, -41, -42, -47, -48, -49, -51, -54, -55])
  have hm := merge_two (literal (valuationOf q) (824)) (literal (valuationOf q) (877)) (literal (valuationOf q) (895)) (countLit q [-1, -3, -6, -8, -9, -10, -15, -16, -17, -20, -24, -26, -27, -30]) (countLit q [-31, -32, -34, -37, -38, -40, -41, -42, -47, -48, -49, -51, -54, -55]) (count889 q) 4 3 (meaning824 q) (meaning877 q) (meaning895 q) hs
  change valuationOf q 824 = false ∨ valuationOf q 877 = false ∨ valuationOf q 895 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause621 (q : Snake 81) (h : Conditions q) : valuation q 824 = false ∨ valuation q 877 = false ∨ valuation q 895 = true := counterClause621 (baseVal q)

theorem counterClause622 (q : Nat → Bool) : valuationOf q 824 = false ∨ valuationOf q 879 = false ∨ valuationOf q 897 = true := by
  have hs : count889 q = (countLit q [-1, -3, -6, -8, -9, -10, -15, -16, -17, -20, -24, -26, -27, -30]) + (countLit q [-31, -32, -34, -37, -38, -40, -41, -42, -47, -48, -49, -51, -54, -55]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -6, -8, -9, -10, -15, -16, -17, -20, -24, -26, -27, -30]) (l₂ := [-31, -32, -34, -37, -38, -40, -41, -42, -47, -48, -49, -51, -54, -55])
  have hm := merge_two (literal (valuationOf q) (824)) (literal (valuationOf q) (879)) (literal (valuationOf q) (897)) (countLit q [-1, -3, -6, -8, -9, -10, -15, -16, -17, -20, -24, -26, -27, -30]) (countLit q [-31, -32, -34, -37, -38, -40, -41, -42, -47, -48, -49, -51, -54, -55]) (count889 q) 4 5 (meaning824 q) (meaning879 q) (meaning897 q) hs
  change valuationOf q 824 = false ∨ valuationOf q 879 = false ∨ valuationOf q 897 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause622 (q : Snake 81) (h : Conditions q) : valuation q 824 = false ∨ valuation q 879 = false ∨ valuation q 897 = true := counterClause622 (baseVal q)

theorem counterClause623 (q : Nat → Bool) : valuationOf q 825 = false ∨ valuationOf q 876 = false ∨ valuationOf q 895 = true := by
  have hs : count889 q = (countLit q [-1, -3, -6, -8, -9, -10, -15, -16, -17, -20, -24, -26, -27, -30]) + (countLit q [-31, -32, -34, -37, -38, -40, -41, -42, -47, -48, -49, -51, -54, -55]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -6, -8, -9, -10, -15, -16, -17, -20, -24, -26, -27, -30]) (l₂ := [-31, -32, -34, -37, -38, -40, -41, -42, -47, -48, -49, -51, -54, -55])
  have hm := merge_two (literal (valuationOf q) (825)) (literal (valuationOf q) (876)) (literal (valuationOf q) (895)) (countLit q [-1, -3, -6, -8, -9, -10, -15, -16, -17, -20, -24, -26, -27, -30]) (countLit q [-31, -32, -34, -37, -38, -40, -41, -42, -47, -48, -49, -51, -54, -55]) (count889 q) 5 2 (meaning825 q) (meaning876 q) (meaning895 q) hs
  change valuationOf q 825 = false ∨ valuationOf q 876 = false ∨ valuationOf q 895 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause623 (q : Snake 81) (h : Conditions q) : valuation q 825 = false ∨ valuation q 876 = false ∨ valuation q 895 = true := counterClause623 (baseVal q)

theorem counterClause624 (q : Nat → Bool) : valuationOf q 826 = false ∨ valuationOf q 875 = false ∨ valuationOf q 895 = true := by
  have hs : count889 q = (countLit q [-1, -3, -6, -8, -9, -10, -15, -16, -17, -20, -24, -26, -27, -30]) + (countLit q [-31, -32, -34, -37, -38, -40, -41, -42, -47, -48, -49, -51, -54, -55]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -6, -8, -9, -10, -15, -16, -17, -20, -24, -26, -27, -30]) (l₂ := [-31, -32, -34, -37, -38, -40, -41, -42, -47, -48, -49, -51, -54, -55])
  have hm := merge_two (literal (valuationOf q) (826)) (literal (valuationOf q) (875)) (literal (valuationOf q) (895)) (countLit q [-1, -3, -6, -8, -9, -10, -15, -16, -17, -20, -24, -26, -27, -30]) (countLit q [-31, -32, -34, -37, -38, -40, -41, -42, -47, -48, -49, -51, -54, -55]) (count889 q) 6 1 (meaning826 q) (meaning875 q) (meaning895 q) hs
  change valuationOf q 826 = false ∨ valuationOf q 875 = false ∨ valuationOf q 895 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause624 (q : Snake 81) (h : Conditions q) : valuation q 826 = false ∨ valuation q 875 = false ∨ valuation q 895 = true := counterClause624 (baseVal q)

theorem counterClause625 (q : Nat → Bool) : valuationOf q 59 = true ∨ valuationOf q 906 = true := by
  have hs : count906 q = (countLit q [-58]) + (countLit q [-59]) := List.countP_append (p := literal q) (l₁ := [-58]) (l₂ := [-59])
  have hm := merge_right (literal (valuationOf q) (-59)) (literal (valuationOf q) (906)) (countLit q [-58]) (countLit q [-59]) (count906 q) 1 (meaningNeg59 q) (meaning906 q) hs
  change (! (valuationOf q 59)) = false ∨ valuationOf q 906 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause625 (q : Snake 81) (h : Conditions q) : valuation q 59 = true ∨ valuation q 906 = true := counterClause625 (baseVal q)

theorem counterClause626 (q : Nat → Bool) : valuationOf q 58 = true ∨ valuationOf q 906 = true := by
  have hs : count906 q = (countLit q [-58]) + (countLit q [-59]) := List.countP_append (p := literal q) (l₁ := [-58]) (l₂ := [-59])
  have hm := merge_left (literal (valuationOf q) (-58)) (literal (valuationOf q) (906)) (countLit q [-58]) (countLit q [-59]) (count906 q) 1 (meaningNeg58 q) (meaning906 q) hs
  change (! (valuationOf q 58)) = false ∨ valuationOf q 906 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause626 (q : Snake 81) (h : Conditions q) : valuation q 58 = true ∨ valuation q 906 = true := counterClause626 (baseVal q)

theorem counterClause627 (q : Nat → Bool) : valuationOf q 58 = true ∨ valuationOf q 59 = true ∨ valuationOf q 907 = true := by
  have hs : count906 q = (countLit q [-58]) + (countLit q [-59]) := List.countP_append (p := literal q) (l₁ := [-58]) (l₂ := [-59])
  have hm := merge_two (literal (valuationOf q) (-58)) (literal (valuationOf q) (-59)) (literal (valuationOf q) (907)) (countLit q [-58]) (countLit q [-59]) (count906 q) 1 1 (meaningNeg58 q) (meaningNeg59 q) (meaning907 q) hs
  change (! (valuationOf q 58)) = false ∨ (! (valuationOf q 59)) = false ∨ valuationOf q 907 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause627 (q : Snake 81) (h : Conditions q) : valuation q 58 = true ∨ valuation q 59 = true ∨ valuation q 907 = true := counterClause627 (baseVal q)

theorem counterClause628 (q : Nat → Bool) : valuationOf q 906 = false ∨ valuationOf q 908 = true := by
  have hs : count908 q = (countLit q [-57]) + (countLit q [-58, -59]) := List.countP_append (p := literal q) (l₁ := [-57]) (l₂ := [-58, -59])
  have hm := merge_right (literal (valuationOf q) (906)) (literal (valuationOf q) (908)) (countLit q [-57]) (countLit q [-58, -59]) (count908 q) 1 (meaning906 q) (meaning908 q) hs
  change valuationOf q 906 = false ∨ valuationOf q 908 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause628 (q : Snake 81) (h : Conditions q) : valuation q 906 = false ∨ valuation q 908 = true := counterClause628 (baseVal q)

theorem counterClause629 (q : Nat → Bool) : valuationOf q 57 = true ∨ valuationOf q 908 = true := by
  have hs : count908 q = (countLit q [-57]) + (countLit q [-58, -59]) := List.countP_append (p := literal q) (l₁ := [-57]) (l₂ := [-58, -59])
  have hm := merge_left (literal (valuationOf q) (-57)) (literal (valuationOf q) (908)) (countLit q [-57]) (countLit q [-58, -59]) (count908 q) 1 (meaningNeg57 q) (meaning908 q) hs
  change (! (valuationOf q 57)) = false ∨ valuationOf q 908 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause629 (q : Snake 81) (h : Conditions q) : valuation q 57 = true ∨ valuation q 908 = true := counterClause629 (baseVal q)

theorem counterClause630 (q : Nat → Bool) : valuationOf q 57 = true ∨ valuationOf q 906 = false ∨ valuationOf q 909 = true := by
  have hs : count908 q = (countLit q [-57]) + (countLit q [-58, -59]) := List.countP_append (p := literal q) (l₁ := [-57]) (l₂ := [-58, -59])
  have hm := merge_two (literal (valuationOf q) (-57)) (literal (valuationOf q) (906)) (literal (valuationOf q) (909)) (countLit q [-57]) (countLit q [-58, -59]) (count908 q) 1 1 (meaningNeg57 q) (meaning906 q) (meaning909 q) hs
  change (! (valuationOf q 57)) = false ∨ valuationOf q 906 = false ∨ valuationOf q 909 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause630 (q : Snake 81) (h : Conditions q) : valuation q 57 = true ∨ valuation q 906 = false ∨ valuation q 909 = true := counterClause630 (baseVal q)

theorem counterClause631 (q : Nat → Bool) : valuationOf q 57 = true ∨ valuationOf q 907 = false ∨ valuationOf q 910 = true := by
  have hs : count908 q = (countLit q [-57]) + (countLit q [-58, -59]) := List.countP_append (p := literal q) (l₁ := [-57]) (l₂ := [-58, -59])
  have hm := merge_two (literal (valuationOf q) (-57)) (literal (valuationOf q) (907)) (literal (valuationOf q) (910)) (countLit q [-57]) (countLit q [-58, -59]) (count908 q) 1 2 (meaningNeg57 q) (meaning907 q) (meaning910 q) hs
  change (! (valuationOf q 57)) = false ∨ valuationOf q 907 = false ∨ valuationOf q 910 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause631 (q : Snake 81) (h : Conditions q) : valuation q 57 = true ∨ valuation q 907 = false ∨ valuation q 910 = true := counterClause631 (baseVal q)

theorem counterClause632 (q : Nat → Bool) : valuationOf q 65 = true ∨ valuationOf q 911 = true := by
  have hs : count911 q = (countLit q [-64]) + (countLit q [-65]) := List.countP_append (p := literal q) (l₁ := [-64]) (l₂ := [-65])
  have hm := merge_right (literal (valuationOf q) (-65)) (literal (valuationOf q) (911)) (countLit q [-64]) (countLit q [-65]) (count911 q) 1 (meaningNeg65 q) (meaning911 q) hs
  change (! (valuationOf q 65)) = false ∨ valuationOf q 911 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause632 (q : Snake 81) (h : Conditions q) : valuation q 65 = true ∨ valuation q 911 = true := counterClause632 (baseVal q)

theorem counterClause633 (q : Nat → Bool) : valuationOf q 64 = true ∨ valuationOf q 911 = true := by
  have hs : count911 q = (countLit q [-64]) + (countLit q [-65]) := List.countP_append (p := literal q) (l₁ := [-64]) (l₂ := [-65])
  have hm := merge_left (literal (valuationOf q) (-64)) (literal (valuationOf q) (911)) (countLit q [-64]) (countLit q [-65]) (count911 q) 1 (meaningNeg64 q) (meaning911 q) hs
  change (! (valuationOf q 64)) = false ∨ valuationOf q 911 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause633 (q : Snake 81) (h : Conditions q) : valuation q 64 = true ∨ valuation q 911 = true := counterClause633 (baseVal q)

theorem counterClause634 (q : Nat → Bool) : valuationOf q 64 = true ∨ valuationOf q 65 = true ∨ valuationOf q 912 = true := by
  have hs : count911 q = (countLit q [-64]) + (countLit q [-65]) := List.countP_append (p := literal q) (l₁ := [-64]) (l₂ := [-65])
  have hm := merge_two (literal (valuationOf q) (-64)) (literal (valuationOf q) (-65)) (literal (valuationOf q) (912)) (countLit q [-64]) (countLit q [-65]) (count911 q) 1 1 (meaningNeg64 q) (meaningNeg65 q) (meaning912 q) hs
  change (! (valuationOf q 64)) = false ∨ (! (valuationOf q 65)) = false ∨ valuationOf q 912 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause634 (q : Snake 81) (h : Conditions q) : valuation q 64 = true ∨ valuation q 65 = true ∨ valuation q 912 = true := counterClause634 (baseVal q)

theorem counterClause635 (q : Nat → Bool) : valuationOf q 70 = true ∨ valuationOf q 913 = true := by
  have hs : count913 q = (countLit q [-67]) + (countLit q [-70]) := List.countP_append (p := literal q) (l₁ := [-67]) (l₂ := [-70])
  have hm := merge_right (literal (valuationOf q) (-70)) (literal (valuationOf q) (913)) (countLit q [-67]) (countLit q [-70]) (count913 q) 1 (meaningNeg70 q) (meaning913 q) hs
  change (! (valuationOf q 70)) = false ∨ valuationOf q 913 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause635 (q : Snake 81) (h : Conditions q) : valuation q 70 = true ∨ valuation q 913 = true := counterClause635 (baseVal q)

theorem counterClause636 (q : Nat → Bool) : valuationOf q 67 = true ∨ valuationOf q 913 = true := by
  have hs : count913 q = (countLit q [-67]) + (countLit q [-70]) := List.countP_append (p := literal q) (l₁ := [-67]) (l₂ := [-70])
  have hm := merge_left (literal (valuationOf q) (-67)) (literal (valuationOf q) (913)) (countLit q [-67]) (countLit q [-70]) (count913 q) 1 (meaningNeg67 q) (meaning913 q) hs
  change (! (valuationOf q 67)) = false ∨ valuationOf q 913 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause636 (q : Snake 81) (h : Conditions q) : valuation q 67 = true ∨ valuation q 913 = true := counterClause636 (baseVal q)

theorem counterClause637 (q : Nat → Bool) : valuationOf q 67 = true ∨ valuationOf q 70 = true ∨ valuationOf q 914 = true := by
  have hs : count913 q = (countLit q [-67]) + (countLit q [-70]) := List.countP_append (p := literal q) (l₁ := [-67]) (l₂ := [-70])
  have hm := merge_two (literal (valuationOf q) (-67)) (literal (valuationOf q) (-70)) (literal (valuationOf q) (914)) (countLit q [-67]) (countLit q [-70]) (count913 q) 1 1 (meaningNeg67 q) (meaningNeg70 q) (meaning914 q) hs
  change (! (valuationOf q 67)) = false ∨ (! (valuationOf q 70)) = false ∨ valuationOf q 914 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause637 (q : Snake 81) (h : Conditions q) : valuation q 67 = true ∨ valuation q 70 = true ∨ valuation q 914 = true := counterClause637 (baseVal q)

theorem counterClause638 (q : Nat → Bool) : valuationOf q 913 = false ∨ valuationOf q 915 = true := by
  have hs : count915 q = (countLit q [-64, -65]) + (countLit q [-67, -70]) := List.countP_append (p := literal q) (l₁ := [-64, -65]) (l₂ := [-67, -70])
  have hm := merge_right (literal (valuationOf q) (913)) (literal (valuationOf q) (915)) (countLit q [-64, -65]) (countLit q [-67, -70]) (count915 q) 1 (meaning913 q) (meaning915 q) hs
  change valuationOf q 913 = false ∨ valuationOf q 915 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause638 (q : Snake 81) (h : Conditions q) : valuation q 913 = false ∨ valuation q 915 = true := counterClause638 (baseVal q)

theorem counterClause639 (q : Nat → Bool) : valuationOf q 914 = false ∨ valuationOf q 916 = true := by
  have hs : count915 q = (countLit q [-64, -65]) + (countLit q [-67, -70]) := List.countP_append (p := literal q) (l₁ := [-64, -65]) (l₂ := [-67, -70])
  have hm := merge_right (literal (valuationOf q) (914)) (literal (valuationOf q) (916)) (countLit q [-64, -65]) (countLit q [-67, -70]) (count915 q) 2 (meaning914 q) (meaning916 q) hs
  change valuationOf q 914 = false ∨ valuationOf q 916 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause639 (q : Snake 81) (h : Conditions q) : valuation q 914 = false ∨ valuation q 916 = true := counterClause639 (baseVal q)

theorem counterClause640 (q : Nat → Bool) : valuationOf q 911 = false ∨ valuationOf q 915 = true := by
  have hs : count915 q = (countLit q [-64, -65]) + (countLit q [-67, -70]) := List.countP_append (p := literal q) (l₁ := [-64, -65]) (l₂ := [-67, -70])
  have hm := merge_left (literal (valuationOf q) (911)) (literal (valuationOf q) (915)) (countLit q [-64, -65]) (countLit q [-67, -70]) (count915 q) 1 (meaning911 q) (meaning915 q) hs
  change valuationOf q 911 = false ∨ valuationOf q 915 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause640 (q : Snake 81) (h : Conditions q) : valuation q 911 = false ∨ valuation q 915 = true := counterClause640 (baseVal q)

theorem block19 (q : Snake 81) (h : Conditions q) : B112E051.Block19 (valuation q) :=
  ⟨clause609 q h, clause610 q h, clause611 q h, clause612 q h, clause613 q h, clause614 q h, clause615 q h, clause616 q h, clause617 q h, clause618 q h, clause619 q h, clause620 q h, clause621 q h, clause622 q h, clause623 q h, clause624 q h, clause625 q h, clause626 q h, clause627 q h, clause628 q h, clause629 q h, clause630 q h, clause631 q h, clause632 q h, clause633 q h, clause634 q h, clause635 q h, clause636 q h, clause637 q h, clause638 q h, clause639 q h, clause640 q h⟩

end
end Snake9.Regrowth.E112051
