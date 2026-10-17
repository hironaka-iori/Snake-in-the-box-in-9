import E112121Semantics
import B112E121Inputs
namespace Snake9.Regrowth.E112121
noncomputable section
local instance blockDec34 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1089 (q : Nat → Bool) : valuationOf q 5 = true ∨ valuationOf q 865 = true := by
  have hs : count865 q = (countLit q [-4]) + (countLit q [-5]) := List.countP_append (p := literal q) (l₁ := [-4]) (l₂ := [-5])
  have hm := merge_right (literal (valuationOf q) (-5)) (literal (valuationOf q) (865)) (countLit q [-4]) (countLit q [-5]) (count865 q) 1 (meaningNeg5 q) (meaning865 q) hs
  change (! (valuationOf q 5)) = false ∨ valuationOf q 865 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1089 (q : Snake 81) (h : Conditions q) : valuation q 5 = true ∨ valuation q 865 = true := counterClause1089 (baseVal q)

theorem counterClause1090 (q : Nat → Bool) : valuationOf q 4 = true ∨ valuationOf q 865 = true := by
  have hs : count865 q = (countLit q [-4]) + (countLit q [-5]) := List.countP_append (p := literal q) (l₁ := [-4]) (l₂ := [-5])
  have hm := merge_left (literal (valuationOf q) (-4)) (literal (valuationOf q) (865)) (countLit q [-4]) (countLit q [-5]) (count865 q) 1 (meaningNeg4 q) (meaning865 q) hs
  change (! (valuationOf q 4)) = false ∨ valuationOf q 865 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1090 (q : Snake 81) (h : Conditions q) : valuation q 4 = true ∨ valuation q 865 = true := counterClause1090 (baseVal q)

theorem counterClause1091 (q : Nat → Bool) : valuationOf q 4 = true ∨ valuationOf q 5 = true ∨ valuationOf q 866 = true := by
  have hs : count865 q = (countLit q [-4]) + (countLit q [-5]) := List.countP_append (p := literal q) (l₁ := [-4]) (l₂ := [-5])
  have hm := merge_two (literal (valuationOf q) (-4)) (literal (valuationOf q) (-5)) (literal (valuationOf q) (866)) (countLit q [-4]) (countLit q [-5]) (count865 q) 1 1 (meaningNeg4 q) (meaningNeg5 q) (meaning866 q) hs
  change (! (valuationOf q 4)) = false ∨ (! (valuationOf q 5)) = false ∨ valuationOf q 866 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1091 (q : Snake 81) (h : Conditions q) : valuation q 4 = true ∨ valuation q 5 = true ∨ valuation q 866 = true := counterClause1091 (baseVal q)

theorem counterClause1092 (q : Nat → Bool) : valuationOf q 865 = false ∨ valuationOf q 867 = true := by
  have hs : count867 q = (countLit q [-1, -3]) + (countLit q [-4, -5]) := List.countP_append (p := literal q) (l₁ := [-1, -3]) (l₂ := [-4, -5])
  have hm := merge_right (literal (valuationOf q) (865)) (literal (valuationOf q) (867)) (countLit q [-1, -3]) (countLit q [-4, -5]) (count867 q) 1 (meaning865 q) (meaning867 q) hs
  change valuationOf q 865 = false ∨ valuationOf q 867 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1092 (q : Snake 81) (h : Conditions q) : valuation q 865 = false ∨ valuation q 867 = true := counterClause1092 (baseVal q)

theorem counterClause1093 (q : Nat → Bool) : valuationOf q 866 = false ∨ valuationOf q 868 = true := by
  have hs : count867 q = (countLit q [-1, -3]) + (countLit q [-4, -5]) := List.countP_append (p := literal q) (l₁ := [-1, -3]) (l₂ := [-4, -5])
  have hm := merge_right (literal (valuationOf q) (866)) (literal (valuationOf q) (868)) (countLit q [-1, -3]) (countLit q [-4, -5]) (count867 q) 2 (meaning866 q) (meaning868 q) hs
  change valuationOf q 866 = false ∨ valuationOf q 868 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1093 (q : Snake 81) (h : Conditions q) : valuation q 866 = false ∨ valuation q 868 = true := counterClause1093 (baseVal q)

theorem counterClause1094 (q : Nat → Bool) : valuationOf q 863 = false ∨ valuationOf q 867 = true := by
  have hs : count867 q = (countLit q [-1, -3]) + (countLit q [-4, -5]) := List.countP_append (p := literal q) (l₁ := [-1, -3]) (l₂ := [-4, -5])
  have hm := merge_left (literal (valuationOf q) (863)) (literal (valuationOf q) (867)) (countLit q [-1, -3]) (countLit q [-4, -5]) (count867 q) 1 (meaning863 q) (meaning867 q) hs
  change valuationOf q 863 = false ∨ valuationOf q 867 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1094 (q : Snake 81) (h : Conditions q) : valuation q 863 = false ∨ valuation q 867 = true := counterClause1094 (baseVal q)

theorem counterClause1095 (q : Nat → Bool) : valuationOf q 863 = false ∨ valuationOf q 865 = false ∨ valuationOf q 868 = true := by
  have hs : count867 q = (countLit q [-1, -3]) + (countLit q [-4, -5]) := List.countP_append (p := literal q) (l₁ := [-1, -3]) (l₂ := [-4, -5])
  have hm := merge_two (literal (valuationOf q) (863)) (literal (valuationOf q) (865)) (literal (valuationOf q) (868)) (countLit q [-1, -3]) (countLit q [-4, -5]) (count867 q) 1 1 (meaning863 q) (meaning865 q) (meaning868 q) hs
  change valuationOf q 863 = false ∨ valuationOf q 865 = false ∨ valuationOf q 868 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1095 (q : Snake 81) (h : Conditions q) : valuation q 863 = false ∨ valuation q 865 = false ∨ valuation q 868 = true := counterClause1095 (baseVal q)

theorem counterClause1096 (q : Nat → Bool) : valuationOf q 863 = false ∨ valuationOf q 866 = false ∨ valuationOf q 869 = true := by
  have hs : count867 q = (countLit q [-1, -3]) + (countLit q [-4, -5]) := List.countP_append (p := literal q) (l₁ := [-1, -3]) (l₂ := [-4, -5])
  have hm := merge_two (literal (valuationOf q) (863)) (literal (valuationOf q) (866)) (literal (valuationOf q) (869)) (countLit q [-1, -3]) (countLit q [-4, -5]) (count867 q) 1 2 (meaning863 q) (meaning866 q) (meaning869 q) hs
  change valuationOf q 863 = false ∨ valuationOf q 866 = false ∨ valuationOf q 869 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1096 (q : Snake 81) (h : Conditions q) : valuation q 863 = false ∨ valuation q 866 = false ∨ valuation q 869 = true := counterClause1096 (baseVal q)

theorem counterClause1097 (q : Nat → Bool) : valuationOf q 864 = false ∨ valuationOf q 868 = true := by
  have hs : count867 q = (countLit q [-1, -3]) + (countLit q [-4, -5]) := List.countP_append (p := literal q) (l₁ := [-1, -3]) (l₂ := [-4, -5])
  have hm := merge_left (literal (valuationOf q) (864)) (literal (valuationOf q) (868)) (countLit q [-1, -3]) (countLit q [-4, -5]) (count867 q) 2 (meaning864 q) (meaning868 q) hs
  change valuationOf q 864 = false ∨ valuationOf q 868 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1097 (q : Snake 81) (h : Conditions q) : valuation q 864 = false ∨ valuation q 868 = true := counterClause1097 (baseVal q)

theorem counterClause1098 (q : Nat → Bool) : valuationOf q 864 = false ∨ valuationOf q 865 = false ∨ valuationOf q 869 = true := by
  have hs : count867 q = (countLit q [-1, -3]) + (countLit q [-4, -5]) := List.countP_append (p := literal q) (l₁ := [-1, -3]) (l₂ := [-4, -5])
  have hm := merge_two (literal (valuationOf q) (864)) (literal (valuationOf q) (865)) (literal (valuationOf q) (869)) (countLit q [-1, -3]) (countLit q [-4, -5]) (count867 q) 2 1 (meaning864 q) (meaning865 q) (meaning869 q) hs
  change valuationOf q 864 = false ∨ valuationOf q 865 = false ∨ valuationOf q 869 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1098 (q : Snake 81) (h : Conditions q) : valuation q 864 = false ∨ valuation q 865 = false ∨ valuation q 869 = true := counterClause1098 (baseVal q)

theorem counterClause1099 (q : Nat → Bool) : valuationOf q 864 = false ∨ valuationOf q 866 = false ∨ valuationOf q 870 = true := by
  have hs : count867 q = (countLit q [-1, -3]) + (countLit q [-4, -5]) := List.countP_append (p := literal q) (l₁ := [-1, -3]) (l₂ := [-4, -5])
  have hm := merge_two (literal (valuationOf q) (864)) (literal (valuationOf q) (866)) (literal (valuationOf q) (870)) (countLit q [-1, -3]) (countLit q [-4, -5]) (count867 q) 2 2 (meaning864 q) (meaning866 q) (meaning870 q) hs
  change valuationOf q 864 = false ∨ valuationOf q 866 = false ∨ valuationOf q 870 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1099 (q : Snake 81) (h : Conditions q) : valuation q 864 = false ∨ valuation q 866 = false ∨ valuation q 870 = true := counterClause1099 (baseVal q)

theorem counterClause1100 (q : Nat → Bool) : valuationOf q 10 = true ∨ valuationOf q 871 = true := by
  have hs : count871 q = (countLit q [-9]) + (countLit q [-10]) := List.countP_append (p := literal q) (l₁ := [-9]) (l₂ := [-10])
  have hm := merge_right (literal (valuationOf q) (-10)) (literal (valuationOf q) (871)) (countLit q [-9]) (countLit q [-10]) (count871 q) 1 (meaningNeg10 q) (meaning871 q) hs
  change (! (valuationOf q 10)) = false ∨ valuationOf q 871 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1100 (q : Snake 81) (h : Conditions q) : valuation q 10 = true ∨ valuation q 871 = true := counterClause1100 (baseVal q)

theorem counterClause1101 (q : Nat → Bool) : valuationOf q 9 = true ∨ valuationOf q 871 = true := by
  have hs : count871 q = (countLit q [-9]) + (countLit q [-10]) := List.countP_append (p := literal q) (l₁ := [-9]) (l₂ := [-10])
  have hm := merge_left (literal (valuationOf q) (-9)) (literal (valuationOf q) (871)) (countLit q [-9]) (countLit q [-10]) (count871 q) 1 (meaningNeg9 q) (meaning871 q) hs
  change (! (valuationOf q 9)) = false ∨ valuationOf q 871 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1101 (q : Snake 81) (h : Conditions q) : valuation q 9 = true ∨ valuation q 871 = true := counterClause1101 (baseVal q)

theorem counterClause1102 (q : Nat → Bool) : valuationOf q 9 = true ∨ valuationOf q 10 = true ∨ valuationOf q 872 = true := by
  have hs : count871 q = (countLit q [-9]) + (countLit q [-10]) := List.countP_append (p := literal q) (l₁ := [-9]) (l₂ := [-10])
  have hm := merge_two (literal (valuationOf q) (-9)) (literal (valuationOf q) (-10)) (literal (valuationOf q) (872)) (countLit q [-9]) (countLit q [-10]) (count871 q) 1 1 (meaningNeg9 q) (meaningNeg10 q) (meaning872 q) hs
  change (! (valuationOf q 9)) = false ∨ (! (valuationOf q 10)) = false ∨ valuationOf q 872 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1102 (q : Snake 81) (h : Conditions q) : valuation q 9 = true ∨ valuation q 10 = true ∨ valuation q 872 = true := counterClause1102 (baseVal q)

theorem counterClause1103 (q : Nat → Bool) : valuationOf q 14 = true ∨ valuationOf q 873 = true := by
  have hs : count873 q = (countLit q [-11]) + (countLit q [-14]) := List.countP_append (p := literal q) (l₁ := [-11]) (l₂ := [-14])
  have hm := merge_right (literal (valuationOf q) (-14)) (literal (valuationOf q) (873)) (countLit q [-11]) (countLit q [-14]) (count873 q) 1 (meaningNeg14 q) (meaning873 q) hs
  change (! (valuationOf q 14)) = false ∨ valuationOf q 873 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1103 (q : Snake 81) (h : Conditions q) : valuation q 14 = true ∨ valuation q 873 = true := counterClause1103 (baseVal q)

theorem counterClause1104 (q : Nat → Bool) : valuationOf q 11 = true ∨ valuationOf q 873 = true := by
  have hs : count873 q = (countLit q [-11]) + (countLit q [-14]) := List.countP_append (p := literal q) (l₁ := [-11]) (l₂ := [-14])
  have hm := merge_left (literal (valuationOf q) (-11)) (literal (valuationOf q) (873)) (countLit q [-11]) (countLit q [-14]) (count873 q) 1 (meaningNeg11 q) (meaning873 q) hs
  change (! (valuationOf q 11)) = false ∨ valuationOf q 873 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1104 (q : Snake 81) (h : Conditions q) : valuation q 11 = true ∨ valuation q 873 = true := counterClause1104 (baseVal q)

theorem counterClause1105 (q : Nat → Bool) : valuationOf q 11 = true ∨ valuationOf q 14 = true ∨ valuationOf q 874 = true := by
  have hs : count873 q = (countLit q [-11]) + (countLit q [-14]) := List.countP_append (p := literal q) (l₁ := [-11]) (l₂ := [-14])
  have hm := merge_two (literal (valuationOf q) (-11)) (literal (valuationOf q) (-14)) (literal (valuationOf q) (874)) (countLit q [-11]) (countLit q [-14]) (count873 q) 1 1 (meaningNeg11 q) (meaningNeg14 q) (meaning874 q) hs
  change (! (valuationOf q 11)) = false ∨ (! (valuationOf q 14)) = false ∨ valuationOf q 874 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1105 (q : Snake 81) (h : Conditions q) : valuation q 11 = true ∨ valuation q 14 = true ∨ valuation q 874 = true := counterClause1105 (baseVal q)

theorem counterClause1106 (q : Nat → Bool) : valuationOf q 873 = false ∨ valuationOf q 875 = true := by
  have hs : count875 q = (countLit q [-9, -10]) + (countLit q [-11, -14]) := List.countP_append (p := literal q) (l₁ := [-9, -10]) (l₂ := [-11, -14])
  have hm := merge_right (literal (valuationOf q) (873)) (literal (valuationOf q) (875)) (countLit q [-9, -10]) (countLit q [-11, -14]) (count875 q) 1 (meaning873 q) (meaning875 q) hs
  change valuationOf q 873 = false ∨ valuationOf q 875 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1106 (q : Snake 81) (h : Conditions q) : valuation q 873 = false ∨ valuation q 875 = true := counterClause1106 (baseVal q)

theorem counterClause1107 (q : Nat → Bool) : valuationOf q 874 = false ∨ valuationOf q 876 = true := by
  have hs : count875 q = (countLit q [-9, -10]) + (countLit q [-11, -14]) := List.countP_append (p := literal q) (l₁ := [-9, -10]) (l₂ := [-11, -14])
  have hm := merge_right (literal (valuationOf q) (874)) (literal (valuationOf q) (876)) (countLit q [-9, -10]) (countLit q [-11, -14]) (count875 q) 2 (meaning874 q) (meaning876 q) hs
  change valuationOf q 874 = false ∨ valuationOf q 876 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1107 (q : Snake 81) (h : Conditions q) : valuation q 874 = false ∨ valuation q 876 = true := counterClause1107 (baseVal q)

theorem counterClause1108 (q : Nat → Bool) : valuationOf q 871 = false ∨ valuationOf q 875 = true := by
  have hs : count875 q = (countLit q [-9, -10]) + (countLit q [-11, -14]) := List.countP_append (p := literal q) (l₁ := [-9, -10]) (l₂ := [-11, -14])
  have hm := merge_left (literal (valuationOf q) (871)) (literal (valuationOf q) (875)) (countLit q [-9, -10]) (countLit q [-11, -14]) (count875 q) 1 (meaning871 q) (meaning875 q) hs
  change valuationOf q 871 = false ∨ valuationOf q 875 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1108 (q : Snake 81) (h : Conditions q) : valuation q 871 = false ∨ valuation q 875 = true := counterClause1108 (baseVal q)

theorem counterClause1109 (q : Nat → Bool) : valuationOf q 871 = false ∨ valuationOf q 873 = false ∨ valuationOf q 876 = true := by
  have hs : count875 q = (countLit q [-9, -10]) + (countLit q [-11, -14]) := List.countP_append (p := literal q) (l₁ := [-9, -10]) (l₂ := [-11, -14])
  have hm := merge_two (literal (valuationOf q) (871)) (literal (valuationOf q) (873)) (literal (valuationOf q) (876)) (countLit q [-9, -10]) (countLit q [-11, -14]) (count875 q) 1 1 (meaning871 q) (meaning873 q) (meaning876 q) hs
  change valuationOf q 871 = false ∨ valuationOf q 873 = false ∨ valuationOf q 876 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1109 (q : Snake 81) (h : Conditions q) : valuation q 871 = false ∨ valuation q 873 = false ∨ valuation q 876 = true := counterClause1109 (baseVal q)

theorem counterClause1110 (q : Nat → Bool) : valuationOf q 871 = false ∨ valuationOf q 874 = false ∨ valuationOf q 877 = true := by
  have hs : count875 q = (countLit q [-9, -10]) + (countLit q [-11, -14]) := List.countP_append (p := literal q) (l₁ := [-9, -10]) (l₂ := [-11, -14])
  have hm := merge_two (literal (valuationOf q) (871)) (literal (valuationOf q) (874)) (literal (valuationOf q) (877)) (countLit q [-9, -10]) (countLit q [-11, -14]) (count875 q) 1 2 (meaning871 q) (meaning874 q) (meaning877 q) hs
  change valuationOf q 871 = false ∨ valuationOf q 874 = false ∨ valuationOf q 877 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1110 (q : Snake 81) (h : Conditions q) : valuation q 871 = false ∨ valuation q 874 = false ∨ valuation q 877 = true := counterClause1110 (baseVal q)

theorem counterClause1111 (q : Nat → Bool) : valuationOf q 872 = false ∨ valuationOf q 876 = true := by
  have hs : count875 q = (countLit q [-9, -10]) + (countLit q [-11, -14]) := List.countP_append (p := literal q) (l₁ := [-9, -10]) (l₂ := [-11, -14])
  have hm := merge_left (literal (valuationOf q) (872)) (literal (valuationOf q) (876)) (countLit q [-9, -10]) (countLit q [-11, -14]) (count875 q) 2 (meaning872 q) (meaning876 q) hs
  change valuationOf q 872 = false ∨ valuationOf q 876 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1111 (q : Snake 81) (h : Conditions q) : valuation q 872 = false ∨ valuation q 876 = true := counterClause1111 (baseVal q)

theorem counterClause1112 (q : Nat → Bool) : valuationOf q 872 = false ∨ valuationOf q 873 = false ∨ valuationOf q 877 = true := by
  have hs : count875 q = (countLit q [-9, -10]) + (countLit q [-11, -14]) := List.countP_append (p := literal q) (l₁ := [-9, -10]) (l₂ := [-11, -14])
  have hm := merge_two (literal (valuationOf q) (872)) (literal (valuationOf q) (873)) (literal (valuationOf q) (877)) (countLit q [-9, -10]) (countLit q [-11, -14]) (count875 q) 2 1 (meaning872 q) (meaning873 q) (meaning877 q) hs
  change valuationOf q 872 = false ∨ valuationOf q 873 = false ∨ valuationOf q 877 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1112 (q : Snake 81) (h : Conditions q) : valuation q 872 = false ∨ valuation q 873 = false ∨ valuation q 877 = true := counterClause1112 (baseVal q)

theorem counterClause1113 (q : Nat → Bool) : valuationOf q 872 = false ∨ valuationOf q 874 = false ∨ valuationOf q 878 = true := by
  have hs : count875 q = (countLit q [-9, -10]) + (countLit q [-11, -14]) := List.countP_append (p := literal q) (l₁ := [-9, -10]) (l₂ := [-11, -14])
  have hm := merge_two (literal (valuationOf q) (872)) (literal (valuationOf q) (874)) (literal (valuationOf q) (878)) (countLit q [-9, -10]) (countLit q [-11, -14]) (count875 q) 2 2 (meaning872 q) (meaning874 q) (meaning878 q) hs
  change valuationOf q 872 = false ∨ valuationOf q 874 = false ∨ valuationOf q 878 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1113 (q : Snake 81) (h : Conditions q) : valuation q 872 = false ∨ valuation q 874 = false ∨ valuation q 878 = true := counterClause1113 (baseVal q)

theorem counterClause1114 (q : Nat → Bool) : valuationOf q 875 = false ∨ valuationOf q 879 = true := by
  have hs : count879 q = (countLit q [-1, -3, -4, -5]) + (countLit q [-9, -10, -11, -14]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -4, -5]) (l₂ := [-9, -10, -11, -14])
  have hm := merge_right (literal (valuationOf q) (875)) (literal (valuationOf q) (879)) (countLit q [-1, -3, -4, -5]) (countLit q [-9, -10, -11, -14]) (count879 q) 1 (meaning875 q) (meaning879 q) hs
  change valuationOf q 875 = false ∨ valuationOf q 879 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1114 (q : Snake 81) (h : Conditions q) : valuation q 875 = false ∨ valuation q 879 = true := counterClause1114 (baseVal q)

theorem counterClause1115 (q : Nat → Bool) : valuationOf q 876 = false ∨ valuationOf q 880 = true := by
  have hs : count879 q = (countLit q [-1, -3, -4, -5]) + (countLit q [-9, -10, -11, -14]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -4, -5]) (l₂ := [-9, -10, -11, -14])
  have hm := merge_right (literal (valuationOf q) (876)) (literal (valuationOf q) (880)) (countLit q [-1, -3, -4, -5]) (countLit q [-9, -10, -11, -14]) (count879 q) 2 (meaning876 q) (meaning880 q) hs
  change valuationOf q 876 = false ∨ valuationOf q 880 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1115 (q : Snake 81) (h : Conditions q) : valuation q 876 = false ∨ valuation q 880 = true := counterClause1115 (baseVal q)

theorem counterClause1116 (q : Nat → Bool) : valuationOf q 877 = false ∨ valuationOf q 881 = true := by
  have hs : count879 q = (countLit q [-1, -3, -4, -5]) + (countLit q [-9, -10, -11, -14]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -4, -5]) (l₂ := [-9, -10, -11, -14])
  have hm := merge_right (literal (valuationOf q) (877)) (literal (valuationOf q) (881)) (countLit q [-1, -3, -4, -5]) (countLit q [-9, -10, -11, -14]) (count879 q) 3 (meaning877 q) (meaning881 q) hs
  change valuationOf q 877 = false ∨ valuationOf q 881 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1116 (q : Snake 81) (h : Conditions q) : valuation q 877 = false ∨ valuation q 881 = true := counterClause1116 (baseVal q)

theorem counterClause1117 (q : Nat → Bool) : valuationOf q 878 = false ∨ valuationOf q 882 = true := by
  have hs : count879 q = (countLit q [-1, -3, -4, -5]) + (countLit q [-9, -10, -11, -14]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -4, -5]) (l₂ := [-9, -10, -11, -14])
  have hm := merge_right (literal (valuationOf q) (878)) (literal (valuationOf q) (882)) (countLit q [-1, -3, -4, -5]) (countLit q [-9, -10, -11, -14]) (count879 q) 4 (meaning878 q) (meaning882 q) hs
  change valuationOf q 878 = false ∨ valuationOf q 882 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1117 (q : Snake 81) (h : Conditions q) : valuation q 878 = false ∨ valuation q 882 = true := counterClause1117 (baseVal q)

theorem counterClause1118 (q : Nat → Bool) : valuationOf q 867 = false ∨ valuationOf q 879 = true := by
  have hs : count879 q = (countLit q [-1, -3, -4, -5]) + (countLit q [-9, -10, -11, -14]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -4, -5]) (l₂ := [-9, -10, -11, -14])
  have hm := merge_left (literal (valuationOf q) (867)) (literal (valuationOf q) (879)) (countLit q [-1, -3, -4, -5]) (countLit q [-9, -10, -11, -14]) (count879 q) 1 (meaning867 q) (meaning879 q) hs
  change valuationOf q 867 = false ∨ valuationOf q 879 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1118 (q : Snake 81) (h : Conditions q) : valuation q 867 = false ∨ valuation q 879 = true := counterClause1118 (baseVal q)

theorem counterClause1119 (q : Nat → Bool) : valuationOf q 867 = false ∨ valuationOf q 875 = false ∨ valuationOf q 880 = true := by
  have hs : count879 q = (countLit q [-1, -3, -4, -5]) + (countLit q [-9, -10, -11, -14]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -4, -5]) (l₂ := [-9, -10, -11, -14])
  have hm := merge_two (literal (valuationOf q) (867)) (literal (valuationOf q) (875)) (literal (valuationOf q) (880)) (countLit q [-1, -3, -4, -5]) (countLit q [-9, -10, -11, -14]) (count879 q) 1 1 (meaning867 q) (meaning875 q) (meaning880 q) hs
  change valuationOf q 867 = false ∨ valuationOf q 875 = false ∨ valuationOf q 880 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1119 (q : Snake 81) (h : Conditions q) : valuation q 867 = false ∨ valuation q 875 = false ∨ valuation q 880 = true := counterClause1119 (baseVal q)

theorem counterClause1120 (q : Nat → Bool) : valuationOf q 867 = false ∨ valuationOf q 876 = false ∨ valuationOf q 881 = true := by
  have hs : count879 q = (countLit q [-1, -3, -4, -5]) + (countLit q [-9, -10, -11, -14]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -4, -5]) (l₂ := [-9, -10, -11, -14])
  have hm := merge_two (literal (valuationOf q) (867)) (literal (valuationOf q) (876)) (literal (valuationOf q) (881)) (countLit q [-1, -3, -4, -5]) (countLit q [-9, -10, -11, -14]) (count879 q) 1 2 (meaning867 q) (meaning876 q) (meaning881 q) hs
  change valuationOf q 867 = false ∨ valuationOf q 876 = false ∨ valuationOf q 881 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1120 (q : Snake 81) (h : Conditions q) : valuation q 867 = false ∨ valuation q 876 = false ∨ valuation q 881 = true := counterClause1120 (baseVal q)

theorem block34 (q : Snake 81) (h : Conditions q) : B112E121.Block34 (valuation q) :=
  ⟨clause1089 q h, clause1090 q h, clause1091 q h, clause1092 q h, clause1093 q h, clause1094 q h, clause1095 q h, clause1096 q h, clause1097 q h, clause1098 q h, clause1099 q h, clause1100 q h, clause1101 q h, clause1102 q h, clause1103 q h, clause1104 q h, clause1105 q h, clause1106 q h, clause1107 q h, clause1108 q h, clause1109 q h, clause1110 q h, clause1111 q h, clause1112 q h, clause1113 q h, clause1114 q h, clause1115 q h, clause1116 q h, clause1117 q h, clause1118 q h, clause1119 q h, clause1120 q h⟩

end
end Snake9.Regrowth.E112121
